import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.EvalForeignConstruction

/-! Public source-facing compiler symbol hooks. The metadata parser and lookup
policy live in the lower-level CompilerForeignSymbolTables module, allowing
CompilerProviders to retain one immutable preparation result without a module
cycle. -/
namespace Miri.Input.CompilerForeignSymbols
open Miri.Interpreter

abbrev Candidate := CompilerForeignSymbolTables.Candidate
abbrev AllocatorTarget := CompilerForeignSymbolTables.AllocatorTarget
abbrev AllocatorEntry := CompilerForeignSymbolTables.AllocatorEntry
abbrev Prepared := CompilerForeignSymbolTables.Prepared

def prepare (instances : CompilerVTableRuntime.Prepared) : Except String Prepared :=
  CompilerForeignSymbolTables.prepare instances

def lookup (prepared : Prepared) (symbol : String) : Except StepError (Option Candidate) :=
  CompilerForeignSymbolTables.lookup prepared symbol

def lookupFunction (prepared : Prepared)
    (loadMir : CallInstance → EStateM StepError S LoadedBody)
    (symbol : String) : EStateM StepError S (Option (LoadedBody × CallInstance)) :=
  CompilerForeignSymbolTables.lookupFunction prepared loadMir symbol

def allocatorSymbol (prepared : Prepared) (symbol : String) :
    Option (ForeignItems.AllocatorSymbol CallInstance) :=
  CompilerForeignSymbolTables.allocatorSymbol prepared symbol

def checkSymbolClash (prepared : Prepared) (symbol : String) : Except StepError Unit :=
  CompilerForeignSymbolTables.checkSymbolClash prepared symbol

def options (prepared : Prepared) (base : EvalForeignConstruction.Options) :
    EvalForeignConstruction.Options :=
  {base with noAllocShimSymbol := prepared.noAllocShimSymbol}

def hooks (prepared : Prepared) (calls : CompilerCallPipeline.Prepared) :
    EvalForeignConstruction.Symbols S := {
  allocatorSymbol := fun symbol => pure (allocatorSymbol prepared symbol)
  lookupFunction := lookupFunction prepared (CompilerCallPipeline.loadMir calls)
  checkSymbolClash := fun symbol => do
    match checkSymbolClash prepared symbol with
    | .ok () => pure ()
    | .error error => throw error }

end Miri.Input.CompilerForeignSymbols
