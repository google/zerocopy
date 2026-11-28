// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `anneal-clang-dump`: Rung-0 C11 / Rung-1 C++20 extractor for Anneal's C/C++
// frontend.
//
// Runs the full Clang preprocessor and Sema over one translation unit, then
// emits a deterministic `RawCppBundle` (schema v1) JSON document containing:
//
//   * the sealed language policy (`LangOptions` + `CodeGenOptions` +
//     `TargetInfo`) that governs the meaning of the captured code,
//   * the bodies of every function reachable through direct calls from the
//     requested `--entry` roots (or from every main-file definition when no
//     root is given), with all implicit casts and integer promotions intact,
//   * declarations (without bodies) of reachable external callees and of
//     callees named by `--externalize-callee` (whose bodies are not
//     traversed),
//   * `ASTRecordLayout` facts for every transitively referenced record, and
//   * Clang CodeGen's ABI classification of every reachable signature.
//
// The extractor keeps control flow, implicit conversions, and evaluation
// structure explicit, folding only compile-time constants (`sizeof`/`alignof`,
// C++ type traits, `if constexpr`, and constexpr-usable integral globals).
// Every construct it does not model is emitted as an explicit `unsupported_*`
// node so that the downstream lowerer (`anneal-lower-cpp`) can fail closed.
//
// For C++ translation units (Rung 1) the extractor works on the post-Sema AST:
// reachable function and class template specializations are emitted as
// separate monomorphic functions and records keyed by their Itanium-mangled
// symbols, methods carry their implicit object parameter explicitly, and every
// non-trivial destructor that the language runs implicitly (automatic locals,
// full-expression temporaries, members, and bases) is recorded so that the
// lowerer can materialize it as an explicit call. Fields that only C++ needs
// are emitted only for C++ translation units, so C output is unchanged.

#include <cstdint>
#include <deque>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/Basic/LangStandard.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/CodeGen/CGFunctionInfo.h"
#include "clang/CodeGen/CodeGenABITypes.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

namespace {

namespace json = llvm::json;

llvm::cl::OptionCategory DumpCategory("anneal-clang-dump options");

llvm::cl::list<std::string> EntryOpt(
    "entry",
    llvm::cl::desc("Root function (unmangled or mangled name). May be given "
                   "more than once. Defaults to every main-file definition."),
    llvm::cl::cat(DumpCategory));

llvm::cl::list<std::string> ExternalizeOpt(
    "externalize-callee",
    llvm::cl::desc("Emit this callee (unqualified, qualified, or mangled name) "
                   "as a bodiless external declaration instead of extracting "
                   "its definition. May be given more than once."),
    llvm::cl::cat(DumpCategory));

llvm::cl::opt<std::string> OutputOpt(
    "output", llvm::cl::desc("Output path for RawCppBundle JSON (default: "
                             "stdout)."),
    llvm::cl::value_desc("path"), llvm::cl::init("-"),
    llvm::cl::cat(DumpCategory));

constexpr int64_t kSchemaVersion = 1;

// Mirrors CodeGen's `TypeHasMayAlias`: a type may alias anything if its tag
// declaration or any typedef in its sugar chain carries `may_alias`.
bool typeHasMayAlias(clang::QualType QT) {
  if (QT.isNull()) return false;
  if (const clang::TagDecl *TD = QT->getAsTagDecl()) {
    if (TD->hasAttr<clang::MayAliasAttr>()) return true;
  }
  while (const auto *TT = QT->getAs<clang::TypedefType>()) {
    if (TT->getDecl()->hasAttr<clang::MayAliasAttr>()) return true;
    QT = TT->desugar();
  }
  return false;
}

class BundleBuilder {
 public:
  BundleBuilder(clang::ASTContext &Ctx, clang::CompilerInstance &CI)
      : Ctx(Ctx),
        CI(CI),
        Mangler(Ctx.createMangleContext()),
        Cxx(Ctx.getLangOpts().CPlusPlus) {
    Gen = clang::CreateLLVMCodeGen(CI, "anneal-clang-dump", LLVMCtx);
    Gen->Initialize(Ctx);
  }

  json::Value build(const std::vector<std::string> &Entries,
                    const std::vector<std::string> &Externalize,
                    std::string &Error) {
    std::vector<const clang::FunctionDecl *> Roots;
    if (!collectRoots(Entries, Externalize, Roots, Error)) return nullptr;

    // Breadth-first reachability over direct calls. Discovery order is a pure
    // function of the source and the root order, so output is deterministic.
    std::deque<const clang::FunctionDecl *> Work(Roots.begin(), Roots.end());
    for (const clang::FunctionDecl *FD : Roots) Seen.insert(FD);
    json::Array Functions;
    while (!Work.empty()) {
      const clang::FunctionDecl *FD = Work.front();
      Work.pop_front();
      Functions.push_back(functionJson(FD));
      for (const clang::FunctionDecl *Callee : PendingCallees) {
        if (Seen.insert(Callee).second) Work.push_back(Callee);
      }
      PendingCallees.clear();
    }

    // Records may be discovered while emitting other records' fields.
    json::Array Records;
    for (size_t I = 0; I < RecordOrder.size(); ++I) {
      Records.push_back(recordJson(RecordOrder[I]));
    }

    json::Object Bundle;
    Bundle["schema_version"] = kSchemaVersion;
    Bundle["tu_main_file"] = mainFileBasename();
    Bundle["target_triple"] = Ctx.getTargetInfo().getTriple().str();
    Bundle["lang_policy"] = langPolicyJson();
    Bundle["records"] = std::move(Records);
    Bundle["functions"] = std::move(Functions);
    return json::Value(std::move(Bundle));
  }

 private:
  // ---------------------------------------------------------------------
  // Roots and identity
  // ---------------------------------------------------------------------

  std::string symbolOf(const clang::FunctionDecl *FD) {
    if (Mangler->shouldMangleDeclName(FD)) {
      std::string S;
      llvm::raw_string_ostream OS(S);
      // Constructors and destructors are named by their complete-object
      // variants (`C1` / `D1`), which is what a complete-object call uses.
      if (const auto *CD = llvm::dyn_cast<clang::CXXConstructorDecl>(FD)) {
        Mangler->mangleName(clang::GlobalDecl(CD, clang::Ctor_Complete), OS);
      } else if (const auto *DD = llvm::dyn_cast<clang::CXXDestructorDecl>(FD)) {
        Mangler->mangleName(clang::GlobalDecl(DD, clang::Dtor_Complete), OS);
      } else {
        Mangler->mangleName(clang::GlobalDecl(FD), OS);
      }
      return OS.str();
    }
    return FD->getNameAsString();
  }

  // Canonical representative: the definition if this TU has one, else the
  // first declaration.
  static const clang::FunctionDecl *canonicalFn(const clang::FunctionDecl *FD) {
    const clang::FunctionDecl *Def = nullptr;
    if (FD->hasBody(Def) && Def != nullptr) return Def;
    return FD->getFirstDecl();
  }

  // Collects every non-dependent function in the TU, including methods,
  // implicit special members, and template specializations.
  class FnCollector : public clang::RecursiveASTVisitor<FnCollector> {
   public:
    std::vector<const clang::FunctionDecl *> Fns;
    bool shouldVisitTemplateInstantiations() const { return true; }
    bool shouldVisitImplicitCode() const { return true; }
    bool VisitFunctionDecl(clang::FunctionDecl *FD) {
      // Deduction guides only steer class template argument deduction;
      // they are never called and cannot be mangled.
      if (!FD->isDependentContext() && !llvm::isa<clang::CXXDeductionGuideDecl>(FD)) {
        Fns.push_back(FD);
      }
      return true;
    }
  };

  // True if `FD` is named by `Name` (unqualified, qualified, or mangled).
  bool namedBy(const clang::FunctionDecl *FD, const std::string &Name) {
    return FD->getNameAsString() == Name || symbolOf(FD) == Name ||
           FD->getQualifiedNameAsString() == Name;
  }

  bool collectRoots(const std::vector<std::string> &Entries,
                    const std::vector<std::string> &Externalize,
                    std::vector<const clang::FunctionDecl *> &Roots,
                    std::string &Error) {
    const clang::SourceManager &SM = Ctx.getSourceManager();
    std::vector<const clang::FunctionDecl *> All;
    if (Cxx) {
      FnCollector C;
      C.TraverseDecl(Ctx.getTranslationUnitDecl());
      All = std::move(C.Fns);
    } else {
      for (const clang::Decl *D : Ctx.getTranslationUnitDecl()->decls()) {
        const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(D);
        if (FD == nullptr) continue;
        All.push_back(FD);
      }
    }
    // Every `--externalize-callee` name must denote a function of this TU,
    // so a misspelled name cannot silently leave a body in the bundle.
    for (const std::string &X : Externalize) {
      bool Found = false;
      for (const clang::FunctionDecl *FD : All) {
        if (namedBy(FD, X)) {
          Externalized.insert(canonicalFn(FD));
          Found = true;
        }
      }
      if (!Found) {
        Error = "externalized callee not found: " + X;
        return false;
      }
    }
    auto AddRoot = [&Roots](const clang::FunctionDecl *FD) {
      for (const clang::FunctionDecl *R : Roots) {
        if (R == FD) return;
      }
      Roots.push_back(FD);
    };
    if (Entries.empty()) {
      for (const clang::FunctionDecl *FD : All) {
        if (FD->doesThisDeclarationHaveABody() && !FD->isImplicit() &&
            SM.isInMainFile(SM.getExpansionLoc(FD->getLocation()))) {
          AddRoot(canonicalFn(FD));
        }
      }
      if (Roots.empty()) {
        Error = "no function definitions found in the main file";
        return false;
      }
      return rootsNotExternalized(Roots, Error);
    }
    for (const std::string &E : Entries) {
      // In C++ one name can denote several specializations of a template;
      // every specialization with a body becomes a separate root.
      bool AnyMatch = false;
      bool AnyBody = false;
      for (const clang::FunctionDecl *FD : All) {
        if (FD->getNameAsString() != E && symbolOf(FD) != E &&
            !(Cxx && FD->getQualifiedNameAsString() == E)) {
          continue;
        }
        AnyMatch = true;
        const clang::FunctionDecl *Found = canonicalFn(FD);
        if (!Found->hasBody()) continue;
        AnyBody = true;
        AddRoot(Found);
        if (!Cxx) break;
      }
      if (!AnyMatch) {
        Error = "entry function not found: " + E;
        return false;
      }
      if (!AnyBody) {
        Error = "entry function has no definition in this TU: " + E;
        return false;
      }
    }
    return rootsNotExternalized(Roots, Error);
  }

  bool rootsNotExternalized(const std::vector<const clang::FunctionDecl *> &Roots,
                            std::string &Error) {
    for (const clang::FunctionDecl *R : Roots) {
      if (Externalized.count(R) != 0) {
        Error = "entry function is also externalized: " + symbolOf(R);
        return false;
      }
    }
    return true;
  }

  std::string mainFileBasename() const {
    const clang::SourceManager &SM = Ctx.getSourceManager();
    clang::OptionalFileEntryRef FE = SM.getFileEntryRefForID(SM.getMainFileID());
    if (!FE) return "<unknown>";
    return llvm::sys::path::filename(FE->getName()).str();
  }

  // ---------------------------------------------------------------------
  // Language policy seal
  // ---------------------------------------------------------------------

  json::Value langPolicyJson() {
    const clang::LangOptions &LO = Ctx.getLangOpts();
    const clang::CodeGenOptions &CGO = CI.getCodeGenOpts();
    json::Object P;
    P["is_cplusplus"] = static_cast<bool>(LO.CPlusPlus);
    P["lang_standard"] =
        clang::LangStandard::getLangStandardForKind(LO.LangStd).getName();
    P["pointer_width_bits"] = static_cast<int64_t>(
        Ctx.getTargetInfo().getPointerWidth(clang::LangAS::Default));
    P["char_is_signed"] = static_cast<bool>(LO.CharIsSigned);
    P["strict_aliasing"] = !CGO.RelaxedAliasing;
    switch (LO.getSignedOverflowBehavior()) {
      case clang::LangOptions::SOB_Undefined:
        P["signed_overflow"] = "iso_ub";
        break;
      case clang::LangOptions::SOB_Defined:
        P["signed_overflow"] = "wrapv";
        break;
      case clang::LangOptions::SOB_Trapping:
        P["signed_overflow"] = "trapping";
        break;
    }
    P["exceptions_enabled"] =
        static_cast<bool>(LO.Exceptions) || static_cast<bool>(LO.CXXExceptions);
    P["fast_math"] = static_cast<bool>(LO.FastMath);
    return json::Value(std::move(P));
  }

  // ---------------------------------------------------------------------
  // Types and records
  // ---------------------------------------------------------------------

  std::string recordIdOf(const clang::RecordDecl *RD) {
    RD = RD->getDefinition() != nullptr
             ? llvm::cast<clang::RecordDecl>(RD->getDefinition())
             : llvm::cast<clang::RecordDecl>(RD->getFirstDecl());
    auto It = RecordIds.find(RD);
    if (It != RecordIds.end()) return It->second;
    std::string Prefix = RD->isUnion() ? "union." : "struct.";
    std::string Name;
    if (Cxx && !RD->getName().empty()) {
      // Qualified name with printed template arguments, e.g.
      // `struct.Span<const unsigned char>` or `struct.ns::Guard`.
      llvm::raw_string_ostream OS(Name);
      RD->getNameForDiagnostic(OS, Ctx.getPrintingPolicy(), /*Qualified=*/true);
      OS.flush();
    } else if (!RD->getName().empty()) {
      Name = RD->getName().str();
    } else if (const clang::TypedefNameDecl *TD =
                   RD->getTypedefNameForAnonDecl()) {
      Name = TD->getName().str();
    } else {
      Name = "anon." + std::to_string(AnonCounter++);
    }
    std::string Id = Prefix + Name;
    // Distinct records with the same spelling (e.g. block-scoped) get a
    // deterministic ordinal suffix.
    std::string Unique = Id;
    for (unsigned N = 1; UsedRecordIds.count(Unique) != 0; ++N) {
      Unique = Id + "." + std::to_string(N);
    }
    UsedRecordIds.insert(Unique);
    RecordIds[RD] = Unique;
    RecordOrder.push_back(RD);
    return Unique;
  }

  json::Value unsupportedType(clang::QualType QT) {
    json::Object O;
    O["kind"] = "unsupported";
    O["desc"] = QT.getAsString();
    return json::Value(std::move(O));
  }

  json::Value typeJson(clang::QualType QT) {
    if (QT.isNull()) {
      json::Object O;
      O["kind"] = "unsupported";
      O["desc"] = "<null type>";
      return json::Value(std::move(O));
    }
    // Volatile accesses are observable side effects that Rung 0 does not
    // model; make every use of a volatile-qualified type fail closed.
    if (QT.isVolatileQualified()) return unsupportedType(QT);
    clang::QualType Canon = Ctx.getCanonicalType(QT);
    const clang::Type *T = Canon.getTypePtr();

    if (const auto *RefT = llvm::dyn_cast<clang::ReferenceType>(T)) {
      // C++ references: the lowerer models them as non-null pointers.
      clang::QualType Pointee = RefT->getPointeeType();
      if (const auto *SRef = QT->getAs<clang::ReferenceType>()) {
        Pointee = SRef->getPointeeType();  // keep `may_alias` sugar visible
      }
      if (Pointee->isFunctionType()) return unsupportedType(QT);
      json::Object O;
      O["kind"] = "ref";
      O["pointee"] = typeJson(Pointee);
      O["is_const"] = Pointee.isConstQualified();
      O["is_rvalue"] = llvm::isa<clang::RValueReferenceType>(RefT);
      O["may_alias"] = typeHasMayAlias(Pointee);
      return json::Value(std::move(O));
    }
    if (const auto *ET = llvm::dyn_cast<clang::EnumType>(T)) {
      const clang::EnumDecl *ED = ET->getDecl()->getDefinition();
      if (ED == nullptr) return unsupportedType(QT);
      return intTypeJson(ED->getIntegerType(), /*AllowCharLike=*/false);
    }
    if (const auto *BT = llvm::dyn_cast<clang::BuiltinType>(T)) {
      if (BT->isVoidType()) {
        json::Object O;
        O["kind"] = "void";
        return json::Value(std::move(O));
      }
      if (BT->isBooleanType()) {
        json::Object O;
        O["kind"] = "bool";
        return json::Value(std::move(O));
      }
      if (BT->isIntegerType()) return intTypeJson(Canon, true);
      if (BT->isNullPtrType()) {
        // `std::nullptr_t`: pointer-sized, with the null pointer as its only
        // value ([basic.fundamental]p15).
        json::Object O;
        O["kind"] = "nullptr_t";
        return json::Value(std::move(O));
      }
      return unsupportedType(QT);
    }
    if (const auto *PT = llvm::dyn_cast<clang::PointerType>(T)) {
      // Use the sugared pointee so `may_alias` typedefs remain visible.
      clang::QualType Pointee = QT->getAs<clang::PointerType>() != nullptr
                                    ? QT->getAs<clang::PointerType>()
                                          ->getPointeeType()
                                    : PT->getPointeeType();
      if (Pointee->isFunctionType()) return unsupportedType(QT);
      json::Object O;
      O["kind"] = "ptr";
      O["pointee"] = typeJson(Pointee);
      O["is_const"] = Pointee.isConstQualified();
      O["is_restrict"] = Canon.isRestrictQualified();
      O["may_alias"] = typeHasMayAlias(Pointee);
      return json::Value(std::move(O));
    }
    if (const auto *CAT = llvm::dyn_cast<clang::ConstantArrayType>(T)) {
      json::Object O;
      O["kind"] = "array";
      O["elem"] = typeJson(CAT->getElementType());
      O["len"] = static_cast<int64_t>(CAT->getSize().getZExtValue());
      return json::Value(std::move(O));
    }
    if (const auto *RT = llvm::dyn_cast<clang::RecordType>(T)) {
      const clang::RecordDecl *RD = RT->getDecl();
      if (RD->getDefinition() == nullptr) return unsupportedType(QT);
      json::Object O;
      O["kind"] = "record";
      O["id"] = recordIdOf(RD);
      return json::Value(std::move(O));
    }
    return unsupportedType(QT);
  }

  json::Value intTypeJson(clang::QualType QT, bool AllowCharLike) {
    clang::QualType Canon = Ctx.getCanonicalType(QT);
    json::Object O;
    O["kind"] = "int";
    O["bits"] = static_cast<int64_t>(Ctx.getTypeSize(Canon));
    O["signed"] = Canon->isSignedIntegerType();
    O["is_char_like"] = AllowCharLike && Canon->isCharType();
    return json::Value(std::move(O));
  }

  bool hasMutableSubobjectImpl(clang::QualType QT,
                               std::set<const clang::RecordDecl *> &Visited) {
    if (QT.isNull()) return false;
    clang::QualType Base = Ctx.getBaseElementType(QT);
    const auto *RT = Base->getAs<clang::RecordType>();
    if (RT == nullptr) return false;
    const clang::RecordDecl *RD = RT->getDecl()->getDefinition();
    if (RD == nullptr) return true;
    if (!Visited.insert(RD).second) return false;
    if (const auto *CRD = llvm::dyn_cast<clang::CXXRecordDecl>(RD)) {
      if (!CRD->isCompleteDefinition()) return true;
      if (CRD->hasMutableFields()) return true;
      for (const clang::CXXBaseSpecifier &B : CRD->bases()) {
        if (hasMutableSubobjectImpl(B.getType(), Visited)) return true;
      }
      for (const clang::CXXBaseSpecifier &VB : CRD->vbases()) {
        if (hasMutableSubobjectImpl(VB.getType(), Visited)) return true;
      }
    }
    for (const clang::FieldDecl *FD : RD->fields()) {
      if (FD->isMutable() || hasMutableSubobjectImpl(FD->getType(), Visited)) {
        return true;
      }
    }
    return false;
  }

  bool hasMutableSubobject(clang::QualType QT) {
    std::set<const clang::RecordDecl *> Visited;
    return hasMutableSubobjectImpl(QT, Visited);
  }

  class ContainsThisVisitor
      : public clang::RecursiveASTVisitor<ContainsThisVisitor> {
   public:
    bool Found = false;
    bool shouldVisitImplicitCode() const { return true; }
    bool VisitCXXThisExpr(clang::CXXThisExpr *) {
      Found = true;
      return false;
    }
    bool VisitCXXDefaultInitExpr(clang::CXXDefaultInitExpr *DIE) {
      if (DIE->getExpr() == nullptr) {
        Found = true;
        return false;
      }
      TraverseStmt(DIE->getExpr());
      return !Found;
    }
    bool VisitCXXDefaultArgExpr(clang::CXXDefaultArgExpr *DAE) {
      if (DAE->getExpr() == nullptr) {
        Found = true;
        return false;
      }
      TraverseStmt(DAE->getExpr());
      return !Found;
    }
  };

  static bool containsThis(const clang::Stmt *S) {
    if (S == nullptr) return false;
    ContainsThisVisitor V;
    V.TraverseStmt(const_cast<clang::Stmt *>(S));
    return V.Found;
  }

  // Checks whether an expression or statement in a constructor may observe
  // the `this` pointer address (as opposed to reading or writing direct
  // non-reference data members `this->field` by value).
  class ThisObserverVisitor
      : public clang::RecursiveASTVisitor<ThisObserverVisitor> {
   public:
    std::set<const clang::CXXThisExpr *> SafeThis;
    std::set<const clang::CastExpr *> SafeArrayDecay;
    bool Observed = false;
    bool shouldVisitImplicitCode() const { return true; }

    bool VisitMemberExpr(clang::MemberExpr *ME) {
      if (ME->isArrow() && llvm::isa<clang::FieldDecl>(ME->getMemberDecl()) &&
          !ME->getMemberDecl()->getType()->isReferenceType()) {
        if (const auto *TE = llvm::dyn_cast<clang::CXXThisExpr>(
                ME->getBase()->IgnoreParens())) {
          SafeThis.insert(TE);
        }
      }
      return true;
    }

    bool VisitArraySubscriptExpr(clang::ArraySubscriptExpr *AS) {
      if (const auto *CE =
              llvm::dyn_cast<clang::CastExpr>(AS->getBase()->IgnoreParens())) {
        if (CE->getCastKind() == clang::CK_ArrayToPointerDecay) {
          SafeArrayDecay.insert(CE);
        }
      }
      return true;
    }

    bool VisitCXXThisExpr(clang::CXXThisExpr *TE) {
      if (SafeThis.count(TE) == 0) Observed = true;
      return true;
    }

    bool VisitUnaryOperator(clang::UnaryOperator *UO) {
      if (UO->getOpcode() == clang::UO_AddrOf &&
          containsThis(UO->getSubExpr())) {
        Observed = true;
      }
      return true;
    }

    bool VisitCastExpr(clang::CastExpr *CE) {
      if (CE->getCastKind() == clang::CK_ArrayToPointerDecay &&
          SafeArrayDecay.count(CE) == 0 && containsThis(CE->getSubExpr())) {
        Observed = true;
      }
      return true;
    }

    bool VisitVarDecl(clang::VarDecl *VD) {
      if (VD->getType()->isReferenceType() && containsThis(VD->getInit())) {
        Observed = true;
      }
      return true;
    }

    bool VisitCallExpr(clang::CallExpr *CE) {
      const clang::FunctionDecl *Callee = CE->getDirectCallee();
      if (Callee == nullptr || Callee->getBuiltinID() != 0) {
        for (const clang::Expr *A : CE->arguments()) {
          if (containsThis(A)) Observed = true;
        }
        return true;
      }
      unsigned FirstArg = 0;
      if (const auto *MC = llvm::dyn_cast<clang::CXXMemberCallExpr>(CE)) {
        const clang::Expr *Obj = MC->getImplicitObjectArgument();
        if (Obj != nullptr && !Obj->getType()->isPointerType() &&
            containsThis(Obj)) {
          Observed = true;
        }
      } else if (llvm::isa<clang::CXXOperatorCallExpr>(CE)) {
        if (const auto *MD = llvm::dyn_cast<clang::CXXMethodDecl>(Callee);
            MD != nullptr && MD->isInstance() && CE->getNumArgs() > 0) {
          if (containsThis(CE->getArg(0))) Observed = true;
          FirstArg = 1;
        }
      }
      for (unsigned I = 0;
           I < Callee->getNumParams() && FirstArg + I < CE->getNumArgs(); ++I) {
        if (Callee->getParamDecl(I)->getType()->isReferenceType() &&
            containsThis(CE->getArg(FirstArg + I))) {
          Observed = true;
        }
      }
      return true;
    }

    bool VisitCXXConstructExpr(clang::CXXConstructExpr *CCE) {
      const clang::CXXConstructorDecl *CD = CCE->getConstructor();
      if (CD == nullptr) {
        Observed = true;
        return true;
      }
      for (unsigned I = 0; I < CD->getNumParams() && I < CCE->getNumArgs();
           ++I) {
        if (CD->getParamDecl(I)->getType()->isReferenceType() &&
            containsThis(CCE->getArg(I))) {
          Observed = true;
        }
      }
      return true;
    }

    bool VisitCXXDefaultInitExpr(clang::CXXDefaultInitExpr *DIE) {
      if (DIE->getExpr() == nullptr) {
        Observed = true;
      } else {
        TraverseStmt(DIE->getExpr());
      }
      return true;
    }

    bool VisitCXXDefaultArgExpr(clang::CXXDefaultArgExpr *DAE) {
      if (DAE->getExpr() == nullptr) {
        Observed = true;
      } else {
        TraverseStmt(DAE->getExpr());
      }
      return true;
    }
  };

  static bool stmtMayObserveThis(const clang::Stmt *S) {
    if (S == nullptr) return false;
    ThisObserverVisitor V;
    V.TraverseStmt(const_cast<clang::Stmt *>(S));
    return V.Observed;
  }

  bool ctorDefMayObserveThis(const clang::CXXConstructorDecl *CD) {
    const clang::ASTRecordLayout &L = Ctx.getASTRecordLayout(CD->getParent());
    for (const clang::CXXCtorInitializer *I : CD->inits()) {
      if (I->isMemberInitializer()) {
        const clang::FieldDecl *F = I->getMember();
        if (F->getType()->isReferenceType() && containsThis(I->getInit())) {
          return true;
        }
        if (stmtMayObserveThis(I->getInit())) return true;
      } else if (I->isBaseInitializer() && !I->isBaseVirtual()) {
        const clang::CXXRecordDecl *B =
            I->getBaseClass()->getAsCXXRecordDecl();
        if (B == nullptr || L.getBaseClassOffset(B).getQuantity() != 0) {
          return true;
        }
        if (stmtMayObserveThis(I->getInit())) return true;
      } else {
        return true;
      }
    }
    return stmtMayObserveThis(CD->getBody());
  }

  bool ctorDeclMayObserveThis(const clang::CXXConstructorDecl *CD) {
    if (CD->isTrivial() || CD->isDeleted()) return false;
    const clang::FunctionDecl *Def = nullptr;
    if (CD->hasBody(Def) && Def != nullptr) {
      return ctorDefMayObserveThis(llvm::cast<clang::CXXConstructorDecl>(Def));
    }
    // Any non-trivial constructor without an instantiated body in this TU
    // (including out-of-line, non-trivial defaulted, or uninstantiated
    // template specialization constructors) may run in another TU across an
    // external call boundary, so fail closed.
    return true;
  }

  bool hasAddressDependentCtorImpl(
      clang::QualType QT,
      std::set<const clang::CXXRecordDecl *> &Visited) {
    if (QT.isNull()) return false;
    clang::QualType Base = Ctx.getBaseElementType(QT);
    const clang::CXXRecordDecl *CRD = Base->getAsCXXRecordDecl();
    if (CRD == nullptr) return false;
    CRD = CRD->getDefinition();
    if (CRD == nullptr || !CRD->isCompleteDefinition()) return true;
    if (!Visited.insert(CRD).second) return false;
    for (const clang::CXXBaseSpecifier &B : CRD->bases()) {
      if (hasAddressDependentCtorImpl(B.getType(), Visited)) return true;
    }
    for (const clang::CXXBaseSpecifier &VB : CRD->vbases()) {
      if (hasAddressDependentCtorImpl(VB.getType(), Visited)) return true;
    }
    for (const clang::FieldDecl *FD : CRD->fields()) {
      if (hasAddressDependentCtorImpl(FD->getType(), Visited)) return true;
      if (FD->hasInClassInitializer()) {
        const clang::Expr *Init = FD->getInClassInitializer();
        if (Init == nullptr) return true;
        if (FD->getType()->isReferenceType() && containsThis(Init)) {
          return true;
        }
        if (stmtMayObserveThis(Init)) return true;
      }
    }
    for (const clang::CXXConstructorDecl *CD : CRD->ctors()) {
      if (ctorDeclMayObserveThis(CD)) return true;
    }
    for (const clang::Decl *D : CRD->decls()) {
      const auto *FTD = llvm::dyn_cast<clang::FunctionTemplateDecl>(D);
      if (FTD == nullptr) continue;
      if (const auto *TplCD = llvm::dyn_cast<clang::CXXConstructorDecl>(
              FTD->getTemplatedDecl())) {
        if (!TplCD->isDeleted()) return true;
      }
      for (const clang::FunctionDecl *Spec : FTD->specializations()) {
        if (const auto *SCD =
                llvm::dyn_cast<clang::CXXConstructorDecl>(Spec)) {
          if (ctorDeclMayObserveThis(SCD)) return true;
        }
      }
    }
    return false;
  }

  bool hasAddressDependentCtor(clang::QualType QT) {
    std::set<const clang::CXXRecordDecl *> Visited;
    return hasAddressDependentCtorImpl(QT, Visited);
  }

  json::Value recordJson(const clang::RecordDecl *RD) {
    const auto *Def = llvm::cast<clang::RecordDecl>(RD->getDefinition());
    const clang::ASTRecordLayout &L = Ctx.getASTRecordLayout(Def);
    json::Object O;
    O["id"] = RecordIds[RD];
    O["name"] = Def->getName().empty()
                    ? (Def->getTypedefNameForAnonDecl() != nullptr
                           ? Def->getTypedefNameForAnonDecl()->getName().str()
                           : std::string())
                    : Def->getName().str();
    O["is_union"] = Def->isUnion();
    O["size_bytes"] = static_cast<int64_t>(L.getSize().getQuantity());
    O["align_bytes"] = static_cast<int64_t>(L.getAlignment().getQuantity());
    if (Def->hasAttr<clang::PackedAttr>()) O["is_packed"] = true;
    if (Def->hasAttr<clang::MayAliasAttr>()) O["may_alias"] = true;
    json::Array Fields;
    unsigned Idx = 0;
    for (const clang::FieldDecl *FD : Def->fields()) {
      json::Object F;
      F["name"] = FD->getName().str();
      F["offset_bits"] = static_cast<int64_t>(L.getFieldOffset(Idx));
      if (FD->isBitField()) {
        F["bit_width"] = static_cast<int64_t>(FD->getBitWidthValue());
      } else {
        F["bit_width"] = nullptr;
      }
      F["ty"] = typeJson(FD->getType());
      Fields.push_back(std::move(F));
      ++Idx;
    }
    O["fields"] = std::move(Fields);
    if (Cxx) {
      if (const auto *CRD = llvm::dyn_cast<clang::CXXRecordDecl>(Def)) {
        O["is_cxx_record"] = true;
        O["is_polymorphic"] = CRD->isPolymorphic();
        O["is_trivially_copyable"] = CRD->isTriviallyCopyable();
        json::Array Bases;
        for (const clang::CXXBaseSpecifier &B : CRD->bases()) {
          json::Object BO;
          const clang::CXXRecordDecl *BRD = B.getType()->getAsCXXRecordDecl();
          if (BRD == nullptr) continue;
          BO["record_id"] = recordIdOf(BRD);
          BO["is_virtual"] = B.isVirtual();
          BO["offset_bytes"] =
              B.isVirtual() ? json::Value(nullptr)
                            : json::Value(static_cast<int64_t>(
                                  L.getBaseClassOffset(BRD).getQuantity()));
          Bases.push_back(std::move(BO));
        }
        O["bases"] = std::move(Bases);
        O["has_non_trivial_dtor"] = CRD->hasNonTrivialDestructor();
        O["dtor_symbol"] = nonTrivialDtorSymbol(CRD, /*Enqueue=*/false);
        O["has_mutable"] = hasMutableSubobject(Ctx.getRecordType(CRD));
        O["has_address_dependent_ctor"] =
            hasAddressDependentCtor(Ctx.getRecordType(CRD));
      }
    }
    return json::Value(std::move(O));
  }

  // Symbol of the non-trivial destructor of `RD`, or null when destruction is
  // trivial. A non-trivial destructor that Sema never declared (because it
  // was never odr-used) is reported as `"<undeclared>"` so consumers fail
  // closed.
  json::Value nonTrivialDtorSymbol(const clang::CXXRecordDecl *RD, bool Enqueue) {
    if (RD == nullptr || !RD->hasDefinition() || !RD->hasNonTrivialDestructor()) {
      return json::Value(nullptr);
    }
    const clang::CXXDestructorDecl *DD = RD->getDestructor();
    if (DD == nullptr) return json::Value("<undeclared>");
    if (Enqueue) PendingCallees.push_back(canonicalFn(DD));
    return json::Value(symbolOf(DD));
  }

  // Non-trivial destructor for an object of type `QT` (null if trivial).
  // Arrays of non-trivially-destructible objects are `"<array>"`.
  json::Value dtorSymbolForType(clang::QualType QT) {
    QT = Ctx.getCanonicalType(QT);
    if (const clang::ArrayType *AT = Ctx.getAsArrayType(QT)) {
      clang::QualType Elem = Ctx.getBaseElementType(AT);
      const clang::CXXRecordDecl *RD = Elem->getAsCXXRecordDecl();
      if (RD != nullptr && RD->hasDefinition() && RD->hasNonTrivialDestructor()) {
        return json::Value("<array>");
      }
      return json::Value(nullptr);
    }
    return nonTrivialDtorSymbol(QT->getAsCXXRecordDecl(), /*Enqueue=*/true);
  }

  // ---------------------------------------------------------------------
  // ABI witness
  // ---------------------------------------------------------------------

  json::Value abiArgJson(const clang::CodeGen::ABIArgInfo &AI) {
    json::Object O;
    if (AI.isDirect() || AI.isExtend()) {
      llvm::Type *T = AI.getCoerceToType();
      if (T != nullptr && T->isIntegerTy()) {
        O["kind"] = AI.isExtend() ? "extend_int" : "direct_int";
        O["bits"] = static_cast<int64_t>(T->getIntegerBitWidth());
        if (AI.isExtend()) O["sign_ext"] = AI.isSignExt();
      } else if (T != nullptr && T->isPointerTy()) {
        O["kind"] = "direct_ptr";
      } else {
        O["kind"] = "direct_other";
        std::string S;
        llvm::raw_string_ostream OS(S);
        if (T != nullptr) T->print(OS);
        O["desc"] = OS.str();
      }
    } else if (AI.isIgnore()) {
      O["kind"] = "ignore";
    } else if (AI.isIndirect()) {
      O["kind"] = "indirect";
      O["byval"] = AI.getIndirectByVal();
    } else {
      O["kind"] = "other";
      O["desc"] = AI.isExpand()            ? "expand"
                  : AI.isCoerceAndExpand() ? "coerce_and_expand"
                  : AI.isInAlloca()        ? "inalloca"
                  : AI.isIndirectAliased() ? "indirect_aliased"
                                           : "target_specific";
    }
    return json::Value(std::move(O));
  }

  json::Value abiWitnessJson(const clang::FunctionDecl *FD) {
    clang::CanQualType FT = FD->getType()->getCanonicalTypeUnqualified();
    const clang::CodeGen::CGFunctionInfo *FI = nullptr;
    const auto *MD = llvm::dyn_cast<clang::CXXMethodDecl>(FD);
    if (MD != nullptr && MD->isInstance()) {
      // Includes the implicit object parameter. Constructors and destructors
      // are arranged as ordinary methods, which matches the Itanium x86-64
      // complete-object variants (void return, `this` first).
      if (auto Proto = FT.getAs<clang::FunctionProtoType>()) {
        FI = &clang::CodeGen::arrangeCXXMethodType(
            Gen->CGM(), MD->getParent(), Proto.getTypePtr(), MD);
      }
    } else if (auto Proto = FT.getAs<clang::FunctionProtoType>()) {
      FI = &clang::CodeGen::arrangeFreeFunctionType(Gen->CGM(), Proto);
    } else if (auto NoProto = FT.getAs<clang::FunctionNoProtoType>()) {
      FI = &clang::CodeGen::arrangeFreeFunctionType(Gen->CGM(), NoProto);
    }
    json::Object O;
    if (FI == nullptr) {
      O["cc"] = "unknown";
      return json::Value(std::move(O));
    }
    O["cc"] = FI->getEffectiveCallingConvention() == llvm::CallingConv::C
                  ? std::string("c")
                  : "llvm_cc_" + std::to_string(
                                     FI->getEffectiveCallingConvention());
    O["return_passing"] = abiArgJson(FI->getReturnInfo());
    json::Array Params;
    for (const auto &Arg : FI->arguments()) Params.push_back(abiArgJson(Arg.info));
    O["param_passing"] = std::move(Params);
    return json::Value(std::move(O));
  }

  // ---------------------------------------------------------------------
  // Functions
  // ---------------------------------------------------------------------

  json::Value functionJson(const clang::FunctionDecl *FD) {
    VarIds.clear();
    ParamIdx.clear();
    NextVarId = 0;
    const auto *MD = llvm::dyn_cast<clang::CXXMethodDecl>(FD);
    const bool HasThis = Cxx && MD != nullptr && MD->isInstance();
    // The implicit object parameter occupies var id 0 / parameter index 0.
    const unsigned ParamBase = HasThis ? 1 : 0;
    NextVarId = ParamBase;
    for (unsigned I = 0; I < FD->getNumParams(); ++I) {
      const clang::ParmVarDecl *P = FD->getParamDecl(I);
      VarIds[P] = NextVarId++;
      ParamIdx[P] = I + ParamBase;
    }

    json::Object O;
    O["symbol"] = symbolOf(FD);
    O["unmangled_name"] = FD->getNameAsString();
    O["is_extern_c"] = FD->isExternC();
    const clang::FunctionDecl *Def = nullptr;
    // An externalized callee is emitted as a declaration: its body (and
    // everything only its body reaches) is never traversed.
    const bool IsExternalized = Externalized.count(FD) != 0;
    bool HasBody = FD->hasBody(Def) && Def == FD && !IsExternalized;
    O["is_definition"] = HasBody;
    if (IsExternalized) O["is_externalized"] = true;
    O["is_variadic"] = FD->isVariadic();
    O["return_ty"] = typeJson(FD->getReturnType());
    json::Array Params;
    if (HasThis) {
      json::Object PO;
      PO["name"] = "this";
      PO["ty"] = typeJson(MD->getThisType());
      PO["is_this"] = true;
      Params.push_back(std::move(PO));
    }
    for (const clang::ParmVarDecl *P : FD->parameters()) {
      json::Object PO;
      PO["name"] = P->getName().str();
      PO["ty"] = typeJson(P->getType());
      if (Cxx) PO["dtor_symbol"] = dtorSymbolForType(P->getType());
      Params.push_back(std::move(PO));
    }
    O["params"] = std::move(Params);
    O["abi_witness"] = abiWitnessJson(FD);
    if (Cxx) cxxFunctionFacts(FD, MD, HasBody, O);
    if (HasBody) {
      O["body_stmt"] = stmtJson(FD->getBody());
    } else {
      O["body_stmt"] = nullptr;
    }
    return json::Value(std::move(O));
  }

  // C++-only function facts: method kind, constructor initializers, and the
  // member/base destructors that run after a destructor body.
  void cxxFunctionFacts(const clang::FunctionDecl *FD,
                        const clang::CXXMethodDecl *MD, bool HasBody,
                        json::Object &O) {
    O["qualified_name"] = FD->getQualifiedNameAsString();
    const char *Kind = "free";
    if (llvm::isa<clang::CXXConstructorDecl>(FD)) {
      Kind = "ctor";
    } else if (llvm::isa<clang::CXXDestructorDecl>(FD)) {
      Kind = "dtor";
    } else if (MD != nullptr) {
      Kind = "method";
    }
    O["method_kind"] = Kind;
    O["this_record_id"] =
        MD != nullptr ? json::Value(recordIdOf(MD->getParent())) : json::Value(nullptr);
    O["is_const_method"] = MD != nullptr && MD->isConst();
    O["is_virtual"] = MD != nullptr && MD->isVirtual();
    O["is_static_method"] = MD != nullptr && MD->isStatic();
    O["is_trivial"] = FD->isTrivial();
    if (const clang::TemplateArgumentList *TAL =
            FD->getTemplateSpecializationArgs()) {
      std::string S;
      llvm::raw_string_ostream OS(S);
      clang::printTemplateArgumentList(OS, TAL->asArray(), Ctx.getPrintingPolicy());
      O["template_args"] = OS.str();
    } else {
      O["template_args"] = nullptr;
    }
    if (!HasBody) return;
    if (const auto *CD = llvm::dyn_cast<clang::CXXConstructorDecl>(FD)) {
      const clang::ASTRecordLayout &L = Ctx.getASTRecordLayout(CD->getParent());
      json::Array Inits;
      for (const clang::CXXCtorInitializer *I : CD->inits()) {
        json::Object IO;
        if (I->isMemberInitializer()) {
          const clang::FieldDecl *F = I->getMember();
          IO["kind"] = "field";
          IO["record_id"] = recordIdOf(F->getParent());
          IO["field_idx"] = static_cast<int64_t>(F->getFieldIndex());
          IO["init"] = exprJson(I->getInit());
        } else if (I->isBaseInitializer() && !I->isBaseVirtual()) {
          const clang::CXXRecordDecl *B = I->getBaseClass()->getAsCXXRecordDecl();
          IO["kind"] = "base";
          IO["record_id"] = recordIdOf(B);
          IO["offset_bytes"] =
              static_cast<int64_t>(L.getBaseClassOffset(B).getQuantity());
          IO["init"] = exprJson(I->getInit());
        } else {
          IO["kind"] = "unsupported";
          IO["desc"] = I->isDelegatingInitializer()
                           ? "delegating constructor"
                           : (I->isBaseInitializer() && I->isBaseVirtual())
                                 ? "virtual base initializer"
                                 : "indirect member initializer";
        }
        Inits.push_back(std::move(IO));
      }
      O["ctor_inits"] = std::move(Inits);
    }
    if (const auto *DD = llvm::dyn_cast<clang::CXXDestructorDecl>(FD)) {
      const clang::CXXRecordDecl *RD = DD->getParent();
      const clang::ASTRecordLayout &L = Ctx.getASTRecordLayout(RD);
      std::vector<const clang::FieldDecl *> Fields;
      for (const clang::FieldDecl *F : RD->fields()) Fields.push_back(F);
      json::Array MemberDtors;
      for (auto It = Fields.rbegin(); It != Fields.rend(); ++It) {
        json::Value Sym = dtorSymbolForType((*It)->getType());
        if (Sym.kind() == json::Value::Null) continue;
        json::Object MO;
        MO["field_idx"] = static_cast<int64_t>((*It)->getFieldIndex());
        MO["record_id"] = recordIdOf(RD);
        MO["dtor_symbol"] = std::move(Sym);
        MemberDtors.push_back(std::move(MO));
      }
      O["member_dtors"] = std::move(MemberDtors);
      std::vector<clang::CXXBaseSpecifier> Bases(RD->bases_begin(),
                                                 RD->bases_end());
      json::Array BaseDtors;
      for (auto It = Bases.rbegin(); It != Bases.rend(); ++It) {
        const clang::CXXRecordDecl *B = It->getType()->getAsCXXRecordDecl();
        json::Value Sym = nonTrivialDtorSymbol(B, /*Enqueue=*/true);
        if (Sym.kind() == json::Value::Null) continue;
        json::Object BO;
        BO["record_id"] = recordIdOf(B);
        BO["offset_bytes"] =
            It->isVirtual() ? json::Value(nullptr)
                            : json::Value(static_cast<int64_t>(
                                  L.getBaseClassOffset(B).getQuantity()));
        BO["dtor_symbol"] = std::move(Sym);
        BaseDtors.push_back(std::move(BO));
      }
      O["base_dtors"] = std::move(BaseDtors);
    }
  }

  // A function-local `static` object that can never change: const-qualified
  // (no `mutable` members), not thread-local, and constant-initialized, so
  // no initialization guard or dynamic initializer runs. Its value is the
  // same on every call; the lowerer still requires that its address never
  // escapes.
  bool isReadOnlyStaticLocal(const clang::VarDecl *VD) {
    const clang::Expr *Init = VD->getInit();
    return VD->isStaticLocal() && VD->getTLSKind() == clang::VarDecl::TLS_None &&
           VD->getType().isConstant(Ctx) && !VD->getType().isVolatileQualified() &&
           !VD->getType()->isReferenceType() &&
           !hasMutableSubobject(VD->getType()) && Init != nullptr &&
           Init->isConstantInitializer(Ctx, /*ForRef=*/false);
  }

  uint32_t varIdOf(const clang::VarDecl *VD) {
    auto It = VarIds.find(VD);
    if (It != VarIds.end()) return It->second;
    uint32_t Id = NextVarId++;
    VarIds[VD] = Id;
    return Id;
  }

  // ---------------------------------------------------------------------
  // Statements
  // ---------------------------------------------------------------------

  json::Value kindOnly(const char *Kind) {
    json::Object O;
    O["kind"] = Kind;
    return json::Value(std::move(O));
  }

  json::Value unsupportedStmt(const clang::Stmt *S, llvm::StringRef Why = "") {
    json::Object O;
    O["kind"] = "unsupported_stmt";
    std::string Desc = S != nullptr ? S->getStmtClassName() : "<null>";
    if (!Why.empty()) Desc += ": " + Why.str();
    O["desc"] = Desc;
    return json::Value(std::move(O));
  }

  json::Value optStmt(const clang::Stmt *S) {
    return S == nullptr ? json::Value(nullptr) : stmtJson(S);
  }

  // Emits one `decl_stmt` per declared variable into `Out`.
  void declStmtInto(const clang::DeclStmt *DS, json::Array &Out) {
    for (const clang::Decl *D : DS->decls()) {
      if (const auto *VD = llvm::dyn_cast<clang::VarDecl>(D)) {
        const bool StaticConst = isReadOnlyStaticLocal(VD);
        if (!VD->hasLocalStorage() && !StaticConst) {
          Out.push_back(unsupportedStmt(DS, "static or extern local variable"));
          continue;
        }
        if (VD->getType()->isVariableArrayType()) {
          Out.push_back(unsupportedStmt(DS, "variable-length array"));
          continue;
        }
        json::Object O;
        O["kind"] = "decl_stmt";
        O["var_id"] = static_cast<int64_t>(varIdOf(VD));
        O["name"] = VD->getName().str();
        O["ty"] = typeJson(VD->getType());
        if (StaticConst) O["is_static_const"] = true;
        if (Cxx) {
          O["is_ref"] = VD->getType()->isReferenceType();
          O["is_nrvo"] = VD->isNRVOVariable();
          O["dtor_symbol"] = VD->getType()->isReferenceType()
                                 ? json::Value(nullptr)
                                 : dtorSymbolForType(VD->getType());
        }
        if (const clang::Expr *Init = VD->getInit()) {
          O["init"] = exprJson(Init);
        }
        Out.push_back(json::Value(std::move(O)));
      } else if (llvm::isa<clang::TypedefNameDecl, clang::TagDecl,
                           clang::StaticAssertDecl>(D)) {
        // Purely compile-time declarations carry no runtime behavior.
        continue;
      } else {
        Out.push_back(unsupportedStmt(DS, D->getDeclKindName()));
      }
    }
  }

  json::Value stmtJson(const clang::Stmt *S) {
    if (S == nullptr) return kindOnly("null_stmt");
    if (const auto *E = llvm::dyn_cast<clang::Expr>(S)) {
      json::Object O;
      O["kind"] = "expr_stmt";
      O["expr"] = exprJson(E);
      return json::Value(std::move(O));
    }
    switch (S->getStmtClass()) {
      case clang::Stmt::CompoundStmtClass: {
        json::Array Stmts;
        for (const clang::Stmt *Sub : llvm::cast<clang::CompoundStmt>(S)->body()) {
          if (const auto *DS = llvm::dyn_cast<clang::DeclStmt>(Sub)) {
            declStmtInto(DS, Stmts);
          } else {
            Stmts.push_back(stmtJson(Sub));
          }
        }
        json::Object O;
        O["kind"] = "compound";
        O["stmts"] = std::move(Stmts);
        return json::Value(std::move(O));
      }
      case clang::Stmt::DeclStmtClass: {
        json::Array Stmts;
        declStmtInto(llvm::cast<clang::DeclStmt>(S), Stmts);
        if (Stmts.size() == 1) return std::move(Stmts[0]);
        json::Object O;
        O["kind"] = "compound";
        O["stmts"] = std::move(Stmts);
        return json::Value(std::move(O));
      }
      case clang::Stmt::IfStmtClass: {
        const auto *If = llvm::cast<clang::IfStmt>(S);
        if (Cxx && If->isConstexpr() && If->getInit() == nullptr &&
            If->getConditionVariable() == nullptr) {
          // `if constexpr` in a specialization: only the taken branch exists
          // at run time.
          bool Taken = false;
          if (!If->getCond()->EvaluateAsBooleanCondition(Taken, Ctx)) {
            return unsupportedStmt(S, "non-constant if constexpr condition");
          }
          const clang::Stmt *Branch = Taken ? If->getThen() : If->getElse();
          return Branch == nullptr ? kindOnly("null_stmt") : stmtJson(Branch);
        }
        if (If->getInit() != nullptr || If->getConditionVariable() != nullptr ||
            If->isConsteval() || If->isConstexpr()) {
          return unsupportedStmt(S, "if with init/condition variable/consteval");
        }
        json::Object O;
        O["kind"] = "if";
        O["cond"] = exprJson(If->getCond());
        O["then_branch"] = stmtJson(If->getThen());
        if (If->getElse() != nullptr) O["else_branch"] = stmtJson(If->getElse());
        return json::Value(std::move(O));
      }
      case clang::Stmt::WhileStmtClass: {
        const auto *W = llvm::cast<clang::WhileStmt>(S);
        if (W->getConditionVariable() != nullptr) {
          return unsupportedStmt(S, "condition variable");
        }
        json::Object O;
        O["kind"] = "while";
        O["cond"] = exprJson(W->getCond());
        O["body"] = stmtJson(W->getBody());
        return json::Value(std::move(O));
      }
      case clang::Stmt::DoStmtClass: {
        const auto *D = llvm::cast<clang::DoStmt>(S);
        json::Object O;
        O["kind"] = "do_while";
        O["body"] = stmtJson(D->getBody());
        O["cond"] = exprJson(D->getCond());
        return json::Value(std::move(O));
      }
      case clang::Stmt::ForStmtClass: {
        const auto *F = llvm::cast<clang::ForStmt>(S);
        if (F->getConditionVariable() != nullptr) {
          return unsupportedStmt(S, "condition variable");
        }
        json::Object O;
        O["kind"] = "for";
        O["init"] = optStmt(F->getInit());
        O["cond"] = F->getCond() != nullptr ? exprJson(F->getCond())
                                            : json::Value(nullptr);
        O["inc"] = F->getInc() != nullptr ? exprJson(F->getInc())
                                          : json::Value(nullptr);
        O["body"] = stmtJson(F->getBody());
        return json::Value(std::move(O));
      }
      case clang::Stmt::SwitchStmtClass: {
        const auto *Sw = llvm::cast<clang::SwitchStmt>(S);
        if (Sw->getInit() != nullptr || Sw->getConditionVariable() != nullptr) {
          return unsupportedStmt(S, "switch with init/condition variable");
        }
        json::Object O;
        O["kind"] = "switch";
        O["cond"] = exprJson(Sw->getCond());
        O["body"] = stmtJson(Sw->getBody());
        return json::Value(std::move(O));
      }
      case clang::Stmt::CaseStmtClass: {
        const auto *C = llvm::cast<clang::CaseStmt>(S);
        if (C->caseStmtIsGNURange()) return unsupportedStmt(S, "GNU case range");
        clang::Expr::EvalResult R;
        if (!C->getLHS()->EvaluateAsInt(R, Ctx)) {
          return unsupportedStmt(S, "non-constant case label");
        }
        json::Object O;
        O["kind"] = "case";
        O["value_str"] = llvm::toString(R.Val.getInt(), 10);
        O["sub"] = stmtJson(C->getSubStmt());
        return json::Value(std::move(O));
      }
      case clang::Stmt::DefaultStmtClass: {
        json::Object O;
        O["kind"] = "default";
        O["sub"] = stmtJson(llvm::cast<clang::DefaultStmt>(S)->getSubStmt());
        return json::Value(std::move(O));
      }
      case clang::Stmt::BreakStmtClass:
        return kindOnly("break");
      case clang::Stmt::ContinueStmtClass:
        return kindOnly("continue");
      case clang::Stmt::GotoStmtClass: {
        json::Object O;
        O["kind"] = "goto";
        O["label"] = llvm::cast<clang::GotoStmt>(S)->getLabel()->getName().str();
        return json::Value(std::move(O));
      }
      case clang::Stmt::LabelStmtClass: {
        const auto *L = llvm::cast<clang::LabelStmt>(S);
        json::Object O;
        O["kind"] = "label";
        O["label"] = L->getDecl()->getName().str();
        O["sub"] = stmtJson(L->getSubStmt());
        return json::Value(std::move(O));
      }
      case clang::Stmt::ReturnStmtClass: {
        const auto *R = llvm::cast<clang::ReturnStmt>(S);
        json::Object O;
        O["kind"] = "return";
        if (R->getRetValue() != nullptr) O["expr"] = exprJson(R->getRetValue());
        if (Cxx && R->getNRVOCandidate() != nullptr) {
          O["nrvo_var_id"] = static_cast<int64_t>(varIdOf(R->getNRVOCandidate()));
        }
        return json::Value(std::move(O));
      }
      case clang::Stmt::NullStmtClass:
        return kindOnly("null_stmt");
      case clang::Stmt::AttributedStmtClass:
        // `[[likely]]`, `[[fallthrough]]`, ...: no run-time meaning.
        if (Cxx) return stmtJson(llvm::cast<clang::AttributedStmt>(S)->getSubStmt());
        return unsupportedStmt(S);
      default:
        return unsupportedStmt(S);
    }
  }

  // ---------------------------------------------------------------------
  // Expressions
  // ---------------------------------------------------------------------

  json::Object exprBase(const clang::Expr *E, const char *Kind) {
    json::Object O;
    O["kind"] = Kind;
    O["ty"] = typeJson(E->getType());
    O["value_category"] = E->isLValue() ? "lvalue"
                          : E->isXValue() ? "xvalue"
                                          : "prvalue";
    return O;
  }

  json::Value unsupportedExpr(const clang::Expr *E, llvm::StringRef Why = "") {
    json::Object O = exprBase(E, "unsupported_expr");
    std::string Desc = E->getStmtClassName();
    if (!Why.empty()) Desc += ": " + Why.str();
    O["desc"] = Desc;
    return json::Value(std::move(O));
  }

  json::Value intLit(const clang::Expr *E, const llvm::APSInt &V) {
    json::Object O = exprBase(E, "int_lit");
    O["value_str"] = llvm::toString(V, 10);
    clang::QualType Canon = Ctx.getCanonicalType(E->getType());
    // Describe an enumeration by its underlying integer type, as `typeJson`
    // does (`isSignedIntegerType` is false for every scoped enumeration).
    if (const auto *ET = Canon->getAs<clang::EnumType>()) {
      if (const clang::EnumDecl *ED = ET->getDecl()->getDefinition()) {
        Canon = Ctx.getCanonicalType(ED->getIntegerType());
      }
    }
    O["bits"] = static_cast<int64_t>(Ctx.getTypeSize(Canon));
    O["signed"] = Canon->isSignedIntegerType();
    return json::Value(std::move(O));
  }

  static const char *unaryOpName(clang::UnaryOperatorKind K) {
    switch (K) {
      case clang::UO_Plus: return "plus";
      case clang::UO_Minus: return "minus";
      case clang::UO_Not: return "bit_not";
      case clang::UO_LNot: return "log_not";
      case clang::UO_AddrOf: return "addr_of";
      case clang::UO_Deref: return "deref";
      case clang::UO_PreInc: return "pre_inc";
      case clang::UO_PreDec: return "pre_dec";
      case clang::UO_PostInc: return "post_inc";
      case clang::UO_PostDec: return "post_dec";
      default: return nullptr;
    }
  }

  static const char *binaryOpName(clang::BinaryOperatorKind K) {
    switch (K) {
      case clang::BO_Add: return "add";
      case clang::BO_Sub: return "sub";
      case clang::BO_Mul: return "mul";
      case clang::BO_Div: return "div";
      case clang::BO_Rem: return "rem";
      case clang::BO_Shl: return "shl";
      case clang::BO_Shr: return "shr";
      case clang::BO_And: return "bit_and";
      case clang::BO_Or: return "bit_or";
      case clang::BO_Xor: return "bit_xor";
      case clang::BO_EQ: return "eq";
      case clang::BO_NE: return "ne";
      case clang::BO_LT: return "lt";
      case clang::BO_LE: return "le";
      case clang::BO_GT: return "gt";
      case clang::BO_GE: return "ge";
      case clang::BO_LAnd: return "log_and";
      case clang::BO_LOr: return "log_or";
      case clang::BO_Comma: return "comma";
      case clang::BO_Assign: return "assign";
      case clang::BO_AddAssign: return "add_assign";
      case clang::BO_SubAssign: return "sub_assign";
      case clang::BO_MulAssign: return "mul_assign";
      case clang::BO_DivAssign: return "div_assign";
      case clang::BO_RemAssign: return "rem_assign";
      case clang::BO_ShlAssign: return "shl_assign";
      case clang::BO_ShrAssign: return "shr_assign";
      case clang::BO_AndAssign: return "and_assign";
      case clang::BO_OrAssign: return "or_assign";
      case clang::BO_XorAssign: return "xor_assign";
      default: return nullptr;
    }
  }

  // Returns nullptr for cast kinds the lowerer must reject.
  const char *castKindName(const clang::CastExpr *CE) {
    clang::QualType To = Ctx.getCanonicalType(CE->getType());
    clang::QualType From = Ctx.getCanonicalType(CE->getSubExpr()->getType());
    switch (CE->getCastKind()) {
      case clang::CK_LValueToRValue: return "lvalue_to_rvalue";
      case clang::CK_IntegralCast:
        return From->isBooleanType() ? "bool_to_int" : "integral_cast";
      case clang::CK_IntegralToBoolean: return "int_to_bool";
      case clang::CK_BitCast:
        return (To->isPointerType() && From->isPointerType()) ? "pointer_cast"
                                                              : "bit_cast";
      case clang::CK_NullToPointer: return "null_to_pointer";
      case clang::CK_ArrayToPointerDecay: return "array_to_pointer_decay";
      case clang::CK_NoOp: return "noop";
      case clang::CK_ToVoid: return "to_void";
      // Additive extension beyond the v1 enumerated set: `if (p)` / `!p`.
      case clang::CK_PointerToBoolean: return "ptr_to_bool";
      default: return nullptr;
    }
  }

  json::Array paramIsRef(const clang::FunctionDecl *FD) {
    json::Array A;
    for (const clang::ParmVarDecl *P : FD->parameters()) {
      A.push_back(P->getType()->isReferenceType());
    }
    return A;
  }

  // Byte offset of the base subobject reached by a derived-to-base cast, or
  // nullopt when the path crosses a virtual base.
  std::optional<int64_t> baseOffsetOf(const clang::CastExpr *CE) {
    clang::QualType From = CE->getSubExpr()->getType();
    if (const auto *PT = From->getAs<clang::PointerType>()) From = PT->getPointeeType();
    const clang::CXXRecordDecl *Derived = From->getAsCXXRecordDecl();
    int64_t Off = 0;
    for (const clang::CXXBaseSpecifier *B : CE->path()) {
      if (B->isVirtual() || Derived == nullptr) return std::nullopt;
      const clang::CXXRecordDecl *Base = B->getType()->getAsCXXRecordDecl();
      if (Base == nullptr) return std::nullopt;
      Off += Ctx.getASTRecordLayout(Derived).getBaseClassOffset(Base).getQuantity();
      Derived = Base;
    }
    return Off;
  }

  json::Value boolOrIntLit(const clang::Expr *E, const llvm::APSInt &V) {
    if (E->getType()->isBooleanType()) {
      json::Object O = exprBase(E, "bool_lit");
      O["value"] = V.getBoolValue();
      return json::Value(std::move(O));
    }
    return intLit(E, V);
  }

  // `lvalue_to_rvalue` of a constexpr-usable static-storage integral object
  // (e.g. `static constexpr uint64_t kMask = ...;`) folds to its value.
  std::optional<json::Value> foldConstantGlobal(const clang::CastExpr *CE) {
    const clang::Expr *Sub = CE->getSubExpr()->IgnoreParens();
    const clang::ValueDecl *D = nullptr;
    if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(Sub)) {
      D = DRE->getDecl();
    } else if (const auto *ME = llvm::dyn_cast<clang::MemberExpr>(Sub)) {
      D = ME->getMemberDecl();
    }
    const auto *VD = llvm::dyn_cast_or_null<clang::VarDecl>(D);
    if (VD == nullptr || VD->hasLocalStorage() ||
        !VD->isUsableInConstantExpressions(Ctx) ||
        !CE->getType()->isIntegralOrEnumerationType()) {
      return std::nullopt;
    }
    clang::Expr::EvalResult R;
    if (!CE->EvaluateAsInt(R, Ctx)) return std::nullopt;
    return boolOrIntLit(CE, R.Val.getInt());
  }

  // C++-only expression forms. Returns nullopt to fall through to the shared
  // C11 handling.
  std::optional<json::Value> cxxExprJson(const clang::Expr *E) {
    // Wrappers with no run-time meaning of their own.
    if (const auto *S = llvm::dyn_cast<clang::SubstNonTypeTemplateParmExpr>(E)) {
      return exprJson(S->getReplacement());
    }
    if (const auto *D = llvm::dyn_cast<clang::CXXDefaultArgExpr>(E)) {
      return exprJson(D->getExpr());
    }
    if (const auto *D = llvm::dyn_cast<clang::CXXDefaultInitExpr>(E)) {
      return exprJson(D->getExpr());
    }
    if (const auto *R = llvm::dyn_cast<clang::CXXRewrittenBinaryOperator>(E)) {
      return exprJson(R->getSemanticForm());
    }
    // Compile-time traits fold to literals.
    if (llvm::isa<clang::TypeTraitExpr, clang::CXXNoexceptExpr,
                  clang::ArrayTypeTraitExpr, clang::ExpressionTraitExpr,
                  clang::ConceptSpecializationExpr, clang::RequiresExpr,
                  clang::SizeOfPackExpr>(E)) {
      clang::Expr::EvalResult R;
      if (!E->isValueDependent() && E->EvaluateAsInt(R, Ctx)) {
        return boolOrIntLit(E, R.Val.getInt());
      }
      return unsupportedExpr(E, "non-constant trait");
    }
    if (llvm::isa<clang::CXXNullPtrLiteralExpr>(E)) {
      return json::Value(exprBase(E, "nullptr_lit"));
    }
    if (const auto *T = llvm::dyn_cast<clang::CXXThisExpr>(E)) {
      json::Object O = exprBase(E, "cxx_this");
      O["is_implicit"] = T->isImplicit();
      return json::Value(std::move(O));
    }
    if (llvm::isa<clang::CXXScalarValueInitExpr>(E)) {
      return json::Value(exprBase(E, "implicit_value_init"));
    }
    if (const auto *EWC = llvm::dyn_cast<clang::ExprWithCleanups>(E)) {
      json::Object O = exprBase(E, "expr_with_cleanups");
      O["sub"] = exprJson(EWC->getSubExpr());
      return json::Value(std::move(O));
    }
    if (const auto *MT = llvm::dyn_cast<clang::MaterializeTemporaryExpr>(E)) {
      json::Object O = exprBase(E, "materialize_temporary");
      O["sub"] = exprJson(MT->getSubExpr());
      O["lifetime_extended"] = MT->getExtendingDecl() != nullptr;
      return json::Value(std::move(O));
    }
    if (const auto *BT = llvm::dyn_cast<clang::CXXBindTemporaryExpr>(E)) {
      json::Object O = exprBase(E, "bind_temporary");
      O["sub"] = exprJson(BT->getSubExpr());
      const clang::CXXDestructorDecl *DD = BT->getTemporary()->getDestructor();
      if (DD != nullptr) {
        PendingCallees.push_back(canonicalFn(DD));
        O["dtor_symbol"] = symbolOf(DD);
      } else {
        O["dtor_symbol"] = "<undeclared>";
      }
      return json::Value(std::move(O));
    }
    if (const auto *CE = llvm::dyn_cast<clang::CXXConstructExpr>(E)) {
      const clang::CXXConstructorDecl *CD = CE->getConstructor();
      json::Object O = exprBase(E, "construct");
      O["ctor_symbol"] = symbolOf(CD);
      O["record_id"] = recordIdOf(CD->getParent());
      O["is_trivial"] = CD->isTrivial();
      O["is_copy_or_move"] = CD->isCopyOrMoveConstructor();
      O["is_default"] = CD->isDefaultConstructor();
      O["zero_init"] = CE->requiresZeroInitialization();
      O["is_elidable"] = CE->isElidable();
      O["is_array_construct"] = Ctx.getAsArrayType(E->getType()) != nullptr;
      switch (CE->getConstructionKind()) {
        case clang::CXXConstructionKind::Complete:
          O["construction_kind"] = "complete";
          break;
        case clang::CXXConstructionKind::NonVirtualBase:
          O["construction_kind"] = "base";
          break;
        case clang::CXXConstructionKind::VirtualBase:
          O["construction_kind"] = "virtual_base";
          break;
        case clang::CXXConstructionKind::Delegating:
          O["construction_kind"] = "delegating";
          break;
      }
      O["param_is_ref"] = paramIsRef(CD);
      json::Array Args;
      for (const clang::Expr *A : CE->arguments()) Args.push_back(exprJson(A));
      O["args"] = std::move(Args);
      if (!CD->isTrivial()) PendingCallees.push_back(canonicalFn(CD));
      return json::Value(std::move(O));
    }
    if (const auto *BBC = llvm::dyn_cast<clang::BuiltinBitCastExpr>(E)) {
      // `__builtin_bit_cast(To, from)`, the primitive under `std::bit_cast`
      // and `absl::bit_cast`. `sub` is an lvalue of `from_ty`.
      json::Object O = exprBase(E, "builtin_bit_cast");
      O["from_ty"] = typeJson(BBC->getSubExpr()->getType());
      O["sub"] = exprJson(BBC->getSubExpr());
      return json::Value(std::move(O));
    }
    if (const auto *CE = llvm::dyn_cast<clang::CastExpr>(E)) {
      const char *Syntax = llvm::isa<clang::ImplicitCastExpr>(CE)          ? "implicit"
                           : llvm::isa<clang::CStyleCastExpr>(CE)          ? "c_style"
                           : llvm::isa<clang::CXXStaticCastExpr>(CE)       ? "static"
                           : llvm::isa<clang::CXXReinterpretCastExpr>(CE)  ? "reinterpret"
                           : llvm::isa<clang::CXXConstCastExpr>(CE)        ? "const"
                           : llvm::isa<clang::CXXFunctionalCastExpr>(CE)   ? "functional"
                                                                           : nullptr;
      if (Syntax == nullptr) return unsupportedExpr(E, "unsupported C++ cast syntax");
      if (CE->getCastKind() == clang::CK_LValueToRValue) {
        if (std::optional<json::Value> V = foldConstantGlobal(CE)) return V;
      }
      const char *K = castKindName(CE);
      std::optional<int64_t> BaseOff;
      if (K == nullptr) {
        switch (CE->getCastKind()) {
          case clang::CK_UncheckedDerivedToBase:
          case clang::CK_DerivedToBase:
            BaseOff = baseOffsetOf(CE);
            if (!BaseOff) return unsupportedExpr(E, "cast through a virtual base");
            K = "derived_to_base";
            break;
          case clang::CK_ConstructorConversion:
            K = "constructor_conversion";
            break;
          case clang::CK_UserDefinedConversion:
            K = "user_defined_conversion";
            break;
          default:
            break;
        }
      }
      if (K == nullptr) {
        return unsupportedExpr(E, std::string("cast:") + CE->getCastKindName());
      }
      json::Object O = exprBase(E, "cast");
      O["cast_kind"] = K;
      O["is_implicit"] = llvm::isa<clang::ImplicitCastExpr>(CE);
      O["cast_syntax"] = Syntax;
      if (BaseOff) O["base_offset_bytes"] = *BaseOff;
      O["sub"] = exprJson(CE->getSubExpr());
      return json::Value(std::move(O));
    }
    if (const auto *Call = llvm::dyn_cast<clang::CallExpr>(E)) {
      json::Object O = exprBase(E, "call");
      const clang::FunctionDecl *Callee = Call->getDirectCallee();
      const auto *MD = llvm::dyn_cast_or_null<clang::CXXMethodDecl>(Callee);
      const clang::Expr *ImplicitObj = nullptr;
      unsigned FirstArg = 0;
      if (const auto *MC = llvm::dyn_cast<clang::CXXMemberCallExpr>(Call)) {
        ImplicitObj = MC->getImplicitObjectArgument();
        if (ImplicitObj == nullptr || MC->getMethodDecl() == nullptr) {
          return unsupportedExpr(E, "pointer-to-member call");
        }
      } else if (llvm::isa<clang::CXXOperatorCallExpr>(Call) && MD != nullptr &&
                 MD->isInstance()) {
        // Member operator: argument 0 is the object expression.
        ImplicitObj = Call->getArg(0);
        FirstArg = 1;
      }
      if (Callee != nullptr) {
        O["callee_symbol"] = symbolOf(Callee);
        O["is_indirect"] = false;
        const bool TrivialAssign =
            MD != nullptr && MD->isTrivial() &&
            (MD->isCopyAssignmentOperator() || MD->isMoveAssignmentOperator());
        if (TrivialAssign) O["trivial_assign"] = true;
        if (Callee->getBuiltinID() != 0) {
          O["is_builtin"] = true;
        } else if (!TrivialAssign) {
          PendingCallees.push_back(canonicalFn(Callee));
        }
        O["param_is_ref"] = paramIsRef(Callee);
        O["returns_ref"] = Callee->getReturnType()->isReferenceType();
      } else {
        O["callee_symbol"] = nullptr;
        O["is_indirect"] = true;
      }
      O["is_virtual"] = MD != nullptr && MD->isVirtual();
      if (ImplicitObj != nullptr) {
        O["implicit_object"] = exprJson(ImplicitObj);
        O["implicit_object_is_ptr"] = ImplicitObj->getType()->isPointerType();
      }
      json::Array Args;
      for (unsigned I = FirstArg; I < Call->getNumArgs(); ++I) {
        Args.push_back(exprJson(Call->getArg(I)));
      }
      O["args"] = std::move(Args);
      return json::Value(std::move(O));
    }
    return std::nullopt;
  }

  json::Value exprJson(const clang::Expr *E) {
    if (E == nullptr) return json::Value(nullptr);

    if (Cxx) {
      if (std::optional<json::Value> V = cxxExprJson(E)) return std::move(*V);
    } else if (const auto *EWC = llvm::dyn_cast<clang::ExprWithCleanups>(E)) {
      // C has no destructors; Clang still wraps some full-expressions (for
      // example, those containing block-scope compound literals). The
      // wrapper has no run-time meaning in C.
      return exprJson(EWC->getSubExpr());
    }

    if (const auto *IL = llvm::dyn_cast<clang::IntegerLiteral>(E)) {
      llvm::APSInt V(IL->getValue(),
                     !Ctx.getCanonicalType(IL->getType())->isSignedIntegerType());
      return intLit(E, V);
    }
    if (const auto *CL = llvm::dyn_cast<clang::CharacterLiteral>(E)) {
      clang::QualType Canon = Ctx.getCanonicalType(CL->getType());
      llvm::APSInt V(llvm::APInt(Ctx.getTypeSize(Canon), CL->getValue(),
                                 Canon->isSignedIntegerType()),
                     !Canon->isSignedIntegerType());
      return intLit(E, V);
    }
    if (const auto *BL = llvm::dyn_cast<clang::CXXBoolLiteralExpr>(E)) {
      json::Object O = exprBase(E, "bool_lit");
      O["value"] = BL->getValue();
      return json::Value(std::move(O));
    }
    if (const auto *CE = llvm::dyn_cast<clang::ConstantExpr>(E)) {
      return exprJson(CE->getSubExpr());
    }
    if (const auto *DRE = llvm::dyn_cast<clang::DeclRefExpr>(E)) {
      const clang::ValueDecl *D = DRE->getDecl();
      if (const auto *EC = llvm::dyn_cast<clang::EnumConstantDecl>(D)) {
        return intLit(E, EC->getInitVal());
      }
      if (const auto *VD = llvm::dyn_cast<clang::VarDecl>(D)) {
        if (!VD->hasLocalStorage() && !isReadOnlyStaticLocal(VD)) {
          if (VD->isStaticLocal() || VD->getTLSKind() != clang::VarDecl::TLS_None) {
            return unsupportedExpr(
                E, "static-local or thread-local variable: " + VD->getName().str());
          }
          // Additive extension beyond the v1 node set: a file-scope or
          // `extern` object with static storage duration.
          json::Object O = exprBase(E, "global_ref");
          std::string Sym;
          if (Mangler->shouldMangleDeclName(VD)) {
            llvm::raw_string_ostream OS(Sym);
            Mangler->mangleName(clang::GlobalDecl(VD), OS);
            OS.flush();
          } else {
            Sym = VD->getName().str();
          }
          O["symbol"] = Sym;
          O["name"] = VD->getName().str();
          O["has_external_linkage"] = VD->hasExternalFormalLinkage();
          return json::Value(std::move(O));
        }
        json::Object O = exprBase(E, "var_ref");
        O["var_id"] = static_cast<int64_t>(varIdOf(VD));
        if (Cxx) O["is_ref_binding"] = VD->getType()->isReferenceType();
        auto PIt = ParamIdx.find(VD);
        O["is_param"] = PIt != ParamIdx.end();
        if (PIt != ParamIdx.end()) {
          O["param_idx"] = static_cast<int64_t>(PIt->second);
        } else {
          O["param_idx"] = nullptr;
        }
        return json::Value(std::move(O));
      }
      return unsupportedExpr(E, std::string("decl_ref:") + D->getDeclKindName());
    }
    if (const auto *UO = llvm::dyn_cast<clang::UnaryOperator>(E)) {
      if (UO->getOpcode() == clang::UO_Extension) return exprJson(UO->getSubExpr());
      const char *Op = unaryOpName(UO->getOpcode());
      if (Op == nullptr) return unsupportedExpr(E, "unary operator");
      json::Object O = exprBase(E, "unary_op");
      O["op"] = Op;
      O["sub"] = exprJson(UO->getSubExpr());
      return json::Value(std::move(O));
    }
    if (const auto *BO = llvm::dyn_cast<clang::BinaryOperator>(E)) {
      const char *Op = binaryOpName(BO->getOpcode());
      if (Op == nullptr) return unsupportedExpr(E, "binary operator");
      json::Object O = exprBase(E, "binary_op");
      O["op"] = Op;
      O["lhs"] = exprJson(BO->getLHS());
      O["rhs"] = exprJson(BO->getRHS());
      if (const auto *CAO = llvm::dyn_cast<clang::CompoundAssignOperator>(BO)) {
        // C11 6.5.16.2: `E1 op= E2` computes `E1 op E2` in the usual
        // arithmetic conversion type, then converts back to E1's type.
        O["compute_lhs_ty"] = typeJson(CAO->getComputationLHSType());
        O["compute_result_ty"] = typeJson(CAO->getComputationResultType());
      }
      return json::Value(std::move(O));
    }
    if (const auto *CO = llvm::dyn_cast<clang::ConditionalOperator>(E)) {
      json::Object O = exprBase(E, "conditional");
      O["cond"] = exprJson(CO->getCond());
      O["then_expr"] = exprJson(CO->getTrueExpr());
      O["else_expr"] = exprJson(CO->getFalseExpr());
      return json::Value(std::move(O));
    }
    if (const auto *CE = llvm::dyn_cast<clang::CastExpr>(E)) {
      if (!llvm::isa<clang::ImplicitCastExpr, clang::CStyleCastExpr>(CE)) {
        return unsupportedExpr(E, "non-C cast");
      }
      const char *K = castKindName(CE);
      if (K == nullptr) {
        return unsupportedExpr(E, std::string("cast:") + CE->getCastKindName());
      }
      json::Object O = exprBase(E, "cast");
      O["cast_kind"] = K;
      O["is_implicit"] = llvm::isa<clang::ImplicitCastExpr>(CE);
      O["sub"] = exprJson(CE->getSubExpr());
      return json::Value(std::move(O));
    }
    if (const auto *AS = llvm::dyn_cast<clang::ArraySubscriptExpr>(E)) {
      json::Object O = exprBase(E, "array_subscript");
      O["base"] = exprJson(AS->getBase());
      O["idx"] = exprJson(AS->getIdx());
      return json::Value(std::move(O));
    }
    if (const auto *ME = llvm::dyn_cast<clang::MemberExpr>(E)) {
      const auto *FD = llvm::dyn_cast<clang::FieldDecl>(ME->getMemberDecl());
      if (FD == nullptr) return unsupportedExpr(E, "non-field member");
      json::Object O = exprBase(E, "member");
      O["base"] = exprJson(ME->getBase());
      O["is_arrow"] = ME->isArrow();
      O["field_name"] = FD->getName().str();
      O["record_id"] = recordIdOf(FD->getParent());
      O["field_idx"] = static_cast<int64_t>(FD->getFieldIndex());
      if (FD->isBitField()) {
        O["is_bitfield"] = true;
        const clang::ASTRecordLayout &L = Ctx.getASTRecordLayout(FD->getParent());
        O["bit_offset"] = static_cast<int64_t>(L.getFieldOffset(FD->getFieldIndex()));
        O["bit_width"] = static_cast<int64_t>(FD->getBitWidthValue());
        O["field_is_signed"] = FD->getType()->isSignedIntegerOrEnumerationType();
      }
      return json::Value(std::move(O));
    }
    if (const auto *Call = llvm::dyn_cast<clang::CallExpr>(E)) {
      json::Object O = exprBase(E, "call");
      const clang::FunctionDecl *Callee = Call->getDirectCallee();
      if (Callee != nullptr) {
        O["callee_symbol"] = symbolOf(Callee);
        O["is_indirect"] = false;
        if (Callee->getBuiltinID() != 0) {
          O["is_builtin"] = true;
        } else {
          PendingCallees.push_back(canonicalFn(Callee));
        }
      } else {
        O["callee_symbol"] = nullptr;
        O["is_indirect"] = true;
      }
      json::Array Args;
      for (const clang::Expr *A : Call->arguments()) Args.push_back(exprJson(A));
      O["args"] = std::move(Args);
      return json::Value(std::move(O));
    }
    if (const auto *ILE = llvm::dyn_cast<clang::InitListExpr>(E)) {
      // Semantic form: one initializer per element or named member, with
      // omitted members as `implicit_value_init` and omitted trailing array
      // elements described by `array_filler`.
      json::Object O = exprBase(E, "init_list");
      json::Array Inits;
      for (const clang::Expr *I : ILE->inits()) Inits.push_back(exprJson(I));
      O["inits"] = std::move(Inits);
      if (ILE->isTransparent()) O["is_transparent"] = true;
      if (const clang::FieldDecl *UF = ILE->getInitializedFieldInUnion()) {
        O["union_field_idx"] = static_cast<int64_t>(UF->getFieldIndex());
      }
      if (ILE->hasArrayFiller()) O["array_filler"] = exprJson(ILE->getArrayFiller());
      return json::Value(std::move(O));
    }
    if (llvm::isa<clang::ImplicitValueInitExpr>(E)) {
      return json::Value(exprBase(E, "implicit_value_init"));
    }
    if (const auto *CLE = llvm::dyn_cast<clang::CompoundLiteralExpr>(E)) {
      // C99 `(T){...}`: an unnamed object initialized by `init` (an lvalue
      // in C, C11 6.5.2.5p4).
      json::Object O = exprBase(E, "compound_literal");
      O["is_file_scope"] = CLE->isFileScope();
      O["init"] = exprJson(CLE->getInitializer());
      return json::Value(std::move(O));
    }
    if (const auto *UE = llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(E)) {
      clang::Expr::EvalResult R;
      if ((UE->getKind() != clang::UETT_SizeOf &&
           UE->getKind() != clang::UETT_AlignOf &&
           UE->getKind() != clang::UETT_PreferredAlignOf) ||
          !UE->EvaluateAsInt(R, Ctx)) {
        return unsupportedExpr(E, "non-constant or non-sizeof trait");
      }
      json::Object O = exprBase(E, "sizeof_or_alignof");
      O["value_bytes"] = static_cast<int64_t>(R.Val.getInt().getZExtValue());
      return json::Value(std::move(O));
    }
    if (const auto *PE = llvm::dyn_cast<clang::ParenExpr>(E)) {
      json::Object O = exprBase(E, "paren");
      O["sub"] = exprJson(PE->getSubExpr());
      return json::Value(std::move(O));
    }
    return unsupportedExpr(E);
  }

  clang::ASTContext &Ctx;
  clang::CompilerInstance &CI;
  std::unique_ptr<clang::MangleContext> Mangler;
  // True for C++ translation units; gates every C++-only field.
  bool Cxx;
  llvm::LLVMContext LLVMCtx;
  std::unique_ptr<clang::CodeGenerator> Gen;

  std::set<const clang::FunctionDecl *> Seen;
  // Canonical callees named by `--externalize-callee`.
  std::set<const clang::FunctionDecl *> Externalized;
  std::vector<const clang::FunctionDecl *> PendingCallees;

  std::map<const clang::RecordDecl *, std::string> RecordIds;
  std::set<std::string> UsedRecordIds;
  std::vector<const clang::RecordDecl *> RecordOrder;
  unsigned AnonCounter = 0;

  std::map<const clang::VarDecl *, uint32_t> VarIds;
  std::map<const clang::VarDecl *, uint32_t> ParamIdx;
  uint32_t NextVarId = 0;
};

class DumpConsumer : public clang::ASTConsumer {
 public:
  DumpConsumer(clang::CompilerInstance &CI, int &Status)
      : CI(CI), Status(Status) {}

  void HandleTranslationUnit(clang::ASTContext &Ctx) override {
    if (CI.getDiagnostics().hasErrorOccurred()) {
      llvm::errs() << "anneal-clang-dump: refusing to emit a bundle for a TU "
                      "with compile errors\n";
      Status = 1;
      return;
    }
    BundleBuilder B(Ctx, CI);
    std::string Error;
    std::vector<std::string> Entries(EntryOpt.begin(), EntryOpt.end());
    std::vector<std::string> Externalize(ExternalizeOpt.begin(), ExternalizeOpt.end());
    json::Value Bundle = B.build(Entries, Externalize, Error);
    if (!Error.empty()) {
      llvm::errs() << "anneal-clang-dump: " << Error << "\n";
      Status = 1;
      return;
    }
    std::string Text = llvm::formatv("{0:2}", Bundle).str();
    Text += "\n";
    if (OutputOpt == "-") {
      llvm::outs() << Text;
      return;
    }
    std::error_code EC;
    llvm::raw_fd_ostream OS(OutputOpt, EC, llvm::sys::fs::OF_Text);
    if (EC) {
      llvm::errs() << "anneal-clang-dump: cannot open " << OutputOpt << ": "
                   << EC.message() << "\n";
      Status = 1;
      return;
    }
    OS << Text;
  }

 private:
  clang::CompilerInstance &CI;
  int &Status;
};

class DumpAction : public clang::ASTFrontendAction {
 public:
  explicit DumpAction(int &Status) : Status(Status) {}

 protected:
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
      clang::CompilerInstance &CI, llvm::StringRef) override {
    return std::make_unique<DumpConsumer>(CI, Status);
  }

 private:
  int &Status;
};

class DumpActionFactory : public clang::tooling::FrontendActionFactory {
 public:
  explicit DumpActionFactory(int &Status) : Status(Status) {}
  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<DumpAction>(Status);
  }

 private:
  int &Status;
};

}  // namespace

int main(int argc, const char **argv) {
  auto Parser = clang::tooling::CommonOptionsParser::create(
      argc, argv, DumpCategory, llvm::cl::Required,
      "anneal-clang-dump: emit a RawCppBundle (schema v1) for one C11 or "
      "C++20 (-fno-exceptions) TU.\n"
      "Usage: anneal-clang-dump [--entry=<fn>]... [--externalize-callee=<fn>]... "
      "[--output=<path>] <file> -- <compiler flags>\n");
  if (!Parser) {
    llvm::errs() << llvm::toString(Parser.takeError());
    return 1;
  }
  if (Parser->getSourcePathList().size() != 1) {
    llvm::errs() << "anneal-clang-dump: exactly one source file is required\n";
    return 1;
  }
  clang::tooling::ClangTool Tool(Parser->getCompilations(),
                                 Parser->getSourcePathList());
  int Status = 0;
  DumpActionFactory Factory(Status);
  int ToolStatus = Tool.run(&Factory);
  if (ToolStatus != 0) return ToolStatus;
  return Status;
}
