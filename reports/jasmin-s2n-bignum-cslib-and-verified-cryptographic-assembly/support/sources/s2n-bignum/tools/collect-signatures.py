#!/usr/bin/python3
# This script
# (1) Collects function signatures from s2n-bignum.h
# (2) Collects function signatures from the header comment in assembly files,
# (3) Compares whether (1) and (2) are consistent, and
# (4) Prints the buffers of function input/output/temporary as an OCaml list.

# Usage: python3 tools/collect-signatures.py
# Output file: {arm,x86 (both)}/proofs/subroutine_signatures.ml
# Please run this script from the root directory of s2n-bignum.

import os


class FnDecl:
  def __init__(self,
      fnname:str,
      args:list[tuple[str,str,bool]],   # (arg name, type, is const?) list
      return_ty:str,
  ):
    self.fnname = fnname
    self.args = args
    self.return_ty = return_ty

  def __eq__(self, decl2):
    return self.fnname == decl2.fnname and self.args == decl2.args and \
        self.return_ty == decl2.return_ty

  def print(self):
    print(f"- Function name: {self.fnname}")
    print(f"- Return type: {self.return_ty}")
    print("- Args:")
    for (argname, argtype, isconst) in self.args:
      print(f"  - {argname}: {'const ' if isconst else ''}{argtype}")


class FnMemInputOutput:
  def __init__(self,
      meminputs:list[tuple[str,str]], # (arg name, elem count (can be symbolic)) list
      memoutputs:list[tuple[str,str]], # (arg name, elem count (can be symbolic)) list
      temporaries:list[tuple[str,str]], # (arg name, elem count (can be symbolic)) list
  ):
    self.meminputs = meminputs
    self.memoutputs = memoutputs
    self.temporaries = temporaries

  def __eq__(self, io2):
    return self.meminputs == io2.meminputs and self.memoutputs == io2.memoutputs and \
        self.temporaries == decl2.temporaries

def parseFnDecl(s:str, filename:str) -> FnDecl:
  assert s.startswith("extern"), s
  original_lines = s

  s = s.replace("\t", " ")
  # Expand S2N_BIGNUM_STATIC macro to static unconditionally
  s = s.replace("S2N_BIGNUM_STATIC", "static")

  s = s[len("extern"):].strip()

  i = s.find(" ")
  return_ty, s = s[:i], s[i:].strip()

  i = s.find("(")
  name, s = s[:i].strip(), s[i:].strip()

  assert(s[0] == "("), f"{filename}: fn signature does not have '(': '{s}' from '{original_lines}'"
  assert(s[-2:] == ");"), f"{filename}: fn signature does not end with ');': '{s}' from '{original_lines}'"
  ts = s[1:-2].split(",")
  args = []

  for strarg in ts:
    strarg = strarg.strip()
    i = strarg.find(" ")
    argty, strarg = strarg[:i], strarg[i:].strip()
    isconst = False
    if argty == "const":
      isconst = True
      i = strarg.find(" ")
      argty, strarg = strarg[:i], strarg[i:].strip()

    if strarg.startswith("*"):
      # Pointer ty
      argty += "*"
      strarg = strarg[1:]
    i = strarg.find("[")
    if i != -1:
      argty += strarg[i:]
      strarg = strarg[:i]
    argname = strarg
    args.append((argname, argty, isconst))

  return FnDecl(name, args, return_ty)

def getMemInoutFromComment(s:str) -> FnMemInputOutput:
  # Return (array name, byte length)
  def parseArr(s:str):
    # s is something like 'x[n]'
    s = s.strip()
    i = s.find('[')
    if i == -1:
      return None
    i2 = s.rfind(']')

    assert(i2 != -1), f"'{s}'"
    return s[:i], s[i+1:i2]

  def splitUsingCommaOrAnd(s):
    ibegin = 0
    bracket = 0
    paren = 0
    itms = []
    for i in range(0, len(s)):
      if s[i] == '[':
        bracket += 1
      elif s[i] == ']':
        assert(bracket > 0)
        bracket -= 1
      elif s[i] == '(':
        paren += 1
      elif s[i] == ')':
        assert(paren > 0)
        paren -= 1
      elif s[i] == ',' and bracket == 0 and paren == 0:
        itms.append(s[ibegin:i])
        ibegin = i + 1
      elif i + 3 <= len(s) and s[i:i+3] == 'and' and bracket == 0 \
           and paren == 0:
        itms.append(s[ibegin:i])
        ibegin = i + 3
    itms.append(s[ibegin:])
    return itms

  def stripPrefixes(s, prefixes):
    s = s.strip()
    for p in prefixes:
      if s.startswith(p):
        return s[len(p):]
    return s

  ts = s.split(";")
  ts = list(filter(lambda x: x.strip() != "", ts))
  # input
  s0 = stripPrefixes(ts[0], ["inputs", "input"])
  strinputs = splitUsingCommaOrAnd(s0)
  inputs = []
  for s in strinputs:
    a = parseArr(s)
    if a:
      inputs.append(a)

  # output
  s1 = stripPrefixes(ts[1], ["outputs", "output"])
  stroutputs = splitUsingCommaOrAnd(s1)
  outputs = []
  for s in stroutputs:
    if s.strip().startswith("function return") or s.strip().startswith("return"):
      continue
    outputs.append(parseArr(s))

  # temporary buffer
  temporaries = []
  if len(ts) > 2:
    assert len(ts) == 3, ts
    s2 = stripPrefixes(ts[2], ["temporary buffers", "temporary buffer"])
    s2s = splitUsingCommaOrAnd(s2)
    for s in s2s:
      temporaries.append(parseArr(s))

  return FnMemInputOutput(inputs, outputs, temporaries)


###############################################################################
#  STEP 1. Collect function signatures and memory input/outputs from          #
#  include/s2n-bignum.h                                                       #
###############################################################################

header_f = open("include/s2n-bignum.h", "r")
header_lines = list(header_f.readlines())

i = 0
prev_mem_inout = None
fnsigsAndInouts = {}
# Some functions have architecture-specific declarations guarded by
# '#ifdef __x86_64__ ... #else ... #endif' because their ABI differs between
# x86 and arm (e.g. an in-place variant on one arch). For those, record a
# per-architecture override keyed by function name so that the generated
# subroutine_signatures.ml and the consistency checks use the right signature.
fnsigsAndInoutsByArch = {"arm": {}, "x86": {}}
# archctx is None outside any ifdef, or the set of archs the current block
# applies to (e.g. {"x86"} inside '#ifdef __x86_64__', {"arm"} inside its '#else').
archctx = None

while i < len(header_lines):
  l = header_lines[i]
  lstrip = l.strip()
  if lstrip == "#ifdef __x86_64__":
    archctx = {"x86"}
    i += 1
    continue
  if lstrip == "#else" and archctx == {"x86"}:
    archctx = {"arm"}
    i += 1
    continue
  if lstrip == "#endif" and archctx is not None:
    archctx = None
    i += 1
    continue
  if not (l.startswith("extern")):
    i += 1
    continue

  # Found a function declaration. :)
  i_fndecl = i
  fndecl = header_lines[i].strip()
  while not header_lines[i].strip().endswith(";"):
    i += 1
    assert i < len(header_lines), "function declaration did not end!"
    fndecl += " " + header_lines[i].strip()

  # Let's parse function declaration first.
  decl = parseFnDecl(fndecl, "include/s2n-bignum.h")


  # Get the contents of the comments that describe inputs and outputs
  j = i_fndecl - 1
  assert 0 <= j
  comment_inout = header_lines[j].strip().lower()
  if comment_inout[:2] != "//":
    # This can happen if there are consecutive fn decls
    mem_inout = prev_mem_inout

  else:
    assert comment_inout[:2] == "//", "has no input/output comment"
    comment_inout = comment_inout[2:].strip()
    while not ("input" in comment_inout) or not ("output" in comment_inout):
      j -= 1
      assert 0 <= j, "missing input or output in comment"
      c = header_lines[j].strip().lower()
      assert c[:2] == "//", f"missing input or output in comment. comment line number: {j+1}, fndecl line num: {i_fndecl+1}"
      comment_inout = c[2:].strip() + "; " + comment_inout

    # Also parse the comment
    mem_inout = getMemInoutFromComment(comment_inout)

  if archctx is None:
    fnsigsAndInouts[decl.fnname] = (decl, mem_inout)
  else:
    for a in archctx:
      fnsigsAndInoutsByArch[a][decl.fnname] = (decl, mem_inout)
    # Keep a default entry (from whichever branch is seen first) so that
    # generic lookups (existence checks) still succeed.
    fnsigsAndInouts.setdefault(decl.fnname, (decl, mem_inout))

  i += 1
  prev_mem_inout = mem_inout

# Resolve the per-architecture signature/inout for a function name.
def sigInoutForArch(fnname, arch):
  if fnname in fnsigsAndInoutsByArch[arch]:
    return fnsigsAndInoutsByArch[arch][fnname]
  return fnsigsAndInouts[fnname]


###############################################################################
#  STEP 2. Collect function signatures from assembly file comments. Do not    #
#  collect memory input/output info, since the comments have a liberal format.#
###############################################################################

fnsigsFromAsm = dict()

for arch in ["arm", "x86"]:
  fnsigsFromAsm[arch] = dict()
  subdirs = sorted(list(os.listdir(arch)))

  for dirname in subdirs:
    if dirname == "proofs" or dirname == "tutorial":
      continue
    p = os.path.join(arch, dirname)
    if not os.path.isdir(p):
      continue

    asm_files = sorted(list(os.listdir(p)))
    for filename in asm_files:
      if not filename.endswith(".S"):
        continue

      pp = os.path.join(p, filename)

      lines = list(open(pp).readlines())
      i = 0
      while i < len(lines):
        if not lines[i].startswith("//"):
          i += 1
          continue

        if not lines[i][len("//"):].strip().startswith("extern"):
          i += 1
          continue

        # Found a function declaration. :)
        i_fndecl = i
        fndecl = lines[i][len("//"):].strip()
        while not lines[i].strip().endswith(";"):
          i += 1
          assert i < len(lines) and lines[i].startswith("//"), \
              f"{pp}: function declaration does not finish! did it forget ';'? (context: {fndecl})"
          fndecl += " " + lines[i][len("//"):].strip()

        # Let's parse function declaration first.
        decl = parseFnDecl(fndecl, pp)

        if decl.fnname + ".S" != filename:
          print(f"NOTE: function '{decl.fnname}' is in '{filename}'")

        fnsigsFromAsm[arch][decl.fnname] = decl

        # Keep collecting, since a few assembly files have multiple functions
        # in a file
        i += 1

###############################################################################
#  STEP 3. Compare collected function signatures as well as memory in/outs    #
###############################################################################

# A list of functions that are either only in arm or x86
onlyInArm = [
  "aes_xts_decrypt",
  "aes_xts_encrypt",
  "bignum_copy_row_from_table_8n",
  "bignum_copy_row_from_table_16",
  "bignum_copy_row_from_table_32",
  "bignum_emontredc_8n_cdiff",
  "bignum_mod_n256k1",
  "bignum_mod_p256k1",
  "curve25519_x25519_byte",
  "curve25519_x25519_byte_alt",
  "sha3_",
  "mldsa_intt_arm",
  "mldsa_pointwise",
  "mldsa_ntt_arm",
  "mldsa_pointwise_acc_l4",
  "mldsa_pointwise_acc_l5",
  "mldsa_pointwise_acc_l7",
  "mldsa_polyz_unpack_17_arm",
  "mldsa_polyz_unpack_19_arm",
  "mldsa_poly_use_hint_32",
  "mldsa_poly_use_hint_88",
  "mldsa_rej_uniform_eta2_VARIABLE_TIME",
  "mldsa_rej_uniform_eta4_VARIABLE_TIME",
  "mldsa_rej_uniform_VARIABLE_TIME",
  "mlkem_ntt",
  "mlkem_intt",
  "mlkem_mulcache_compute",
  "mlkem_rej_uniform_VARIABLE_TIME",
]
onlyInX86 = [
  "bignum_cmul_p25519_alt",
  "bignum_cmul_p256_alt",
  "bignum_cmul_p256k1_alt",
  "bignum_cmul_p384_alt",
  "bignum_cmul_p521_alt",
  "bignum_cmul_sm2_alt",
  "bignum_deamont_p256_alt",
  "bignum_deamont_p384_alt",
  "bignum_demont_p256_alt",
  "bignum_demont_p384_alt",
  "bignum_mod_n256_alt",
  "bignum_mod_n384_alt",
  "bignum_mod_n521_9_alt",
  "bignum_mod_nsm2_alt",
  "bignum_mod_p256_alt",
  "bignum_mod_p384_alt",
  "bignum_tomont_p256_alt",
  "bignum_tomont_p256k1_alt",
  "bignum_tomont_p384_alt",
  "bignum_triple_p256_alt",
  "bignum_triple_p256k1_alt",
  "bignum_triple_p384_alt",
  "bignum_triple_p521_alt",
  "bignum_triple_sm2_alt",
  "mldsa_intt",
  "mldsa_ntt",
  "mldsa_nttunpack",
  "mldsa_pointwise_acc_l4_x86",
  "mldsa_pointwise_acc_l5_x86",
  "mldsa_pointwise_acc_l7_x86",
  "mldsa_pointwise_x86",
  "mldsa_polyz_unpack_17_x86",
  "mldsa_polyz_unpack_19_x86",
  "mldsa_reduce",
  "mldsa_rej_uniform_VARIABLE_TIME_x86",
  "mldsa_rej_uniform_eta2_VARIABLE_TIME_x86",
  "mldsa_rej_uniform_eta4_VARIABLE_TIME_x86",
  "mlkem_frombytes",
  "mlkem_mulcache_compute_x86",
  "mlkem_ntt_x86",
  "mlkem_intt_x86",
  "mlkem_unpack",
]

for arch in ["arm","x86"]:
  for fnname in fnsigsFromAsm[arch]:
    assert fnname in fnsigsAndInouts, f"{fnname} declaration is missing in s2n-bignum.h"

def checkOnlyInArch(fnname, onlyIn):
  for f in onlyIn:
    if f.endswith("_") and fnname.startswith(f):
      return True
    elif f == fnname:
      return True
  return False

for fnname in fnsigsAndInouts:
  if not checkOnlyInArch(fnname, onlyInX86):
    fnsigFromHeaderArm,_ = sigInoutForArch(fnname, "arm")
    assert fnname in fnsigsFromAsm["arm"], \
      f"Could not find function {fnname} from arm! Should it be added to onlyInX86 array?"
    if fnsigFromHeaderArm != fnsigsFromAsm["arm"][fnname]:
      print(f"Function signature mismatch! function: {fnname}, arch: arm")
      print("s2n-bignum.h:")
      fnsigFromHeaderArm.print()
      print("assembly comment:")
      fnsigsFromAsm["arm"][fnname].print()
      assert fnsigFromHeaderArm == fnsigsFromAsm["arm"][fnname], f"{fnname}"

  if not checkOnlyInArch(fnname, onlyInArm):
    fnsigFromHeaderX86,_ = sigInoutForArch(fnname, "x86")
    assert fnname in fnsigsFromAsm["x86"], \
      f"Could not find function {fnname} from x86! Should it be added to onlyInArm array?"
    if fnsigFromHeaderX86 != fnsigsFromAsm["x86"][fnname]:
      print("Function signature mismatch! function: {fnname}, arch: arm")
      print("s2n-bignum.h:")
      fnsigFromHeaderX86.print()
      print("assembly comment:")
      fnsigsFromAsm["x86"][fnname].print()
      assert fnsigFromHeaderX86 == fnsigsFromAsm["x86"][fnname], f"{fnname}"

for archname in ["arm","x86"]:
  f = open(os.path.join(archname, os.path.join("proofs", "subroutine_signatures.ml")), "w")
  f.write("let subroutine_signatures = [\n")
  fnnames = sorted(list(fnsigsFromAsm[archname].keys()))
  for fnname in fnnames:
    print(f"Printing inpput/output of {fnname}..")

    fnsig = fnsigsFromAsm[archname][fnname]
    _, meminout = sigInoutForArch(fnname, archname)
    f.write(f'("{fnsig.fnname}",\n')

    # args and return type
    f.write(f'  ([(*args*)\n')
    for argname, argtype, isconst in fnsig.args:
      f.write(f'     ("{argname}", "{argtype}", (*is const?*)"{"true" if isconst else "false"}");\n')
    f.write(f'   ],\n')
    f.write(f'   "{fnsig.return_ty}",\n')

    # Before printing input and output buffers, collect elem bytesize of buffers
    arg_elem_bytesizes = dict()
    isPtr = lambda fullty, elemty: fullty.startswith(elemty + "*")
    isPtrOrArray = lambda fullty, elemty: fullty.startswith(elemty + "[") or fullty.startswith(elemty + "*")
    for argname, argtype, _ in fnsig.args:
      if isPtrOrArray(argtype, "int64_t") or isPtrOrArray(argtype, "uint64_t"):
        arg_elem_bytesizes[argname] = 8
      elif isPtrOrArray(argtype, "int32_t") or isPtrOrArray(argtype, "uint32_t"):
        arg_elem_bytesizes[argname] = 4
      elif isPtrOrArray(argtype, "int16_t") or isPtrOrArray(argtype, "uint16_t"):
        arg_elem_bytesizes[argname] = 2
      elif isPtrOrArray(argtype, "int8_t") or isPtrOrArray(argtype, "uint8_t"):
        arg_elem_bytesizes[argname] = 1
      elif isPtr(argtype, "s2n_bignum_AES_KEY"):
        arg_elem_bytesizes[argname] = 1
      elif "[" not in argtype and "*" not in argtype:
        continue
      else:
        assert False, f"Unknown type: {argtype}!"

    # input and output buffers
    f.write(f'   [(* input buffers *)\n')
    for argname, bufferlen in meminout.meminputs:
      f.write(f'    ("{argname}", "{bufferlen}"(* num elems *), {arg_elem_bytesizes[argname]}(* elem bytesize *));\n')
    f.write(f'   ],\n')
    f.write(f'   [(* output buffers *)\n')
    for argname, bufferlen in meminout.memoutputs:
      f.write(f'    ("{argname}", "{bufferlen}"(* num elems *), {arg_elem_bytesizes[argname]}(* elem bytesize *));\n')
    f.write(f'   ],\n')
    f.write(f'   [(* temporary buffers *)\n')
    for argname, bufferlen in meminout.temporaries:
      f.write(f'    ("{argname}", "{bufferlen}"(* num elems *), {arg_elem_bytesizes[argname]}(* elem bytesize *));\n')
    f.write(f'   ])\n')

    f.write(");\n\n")
  f.write("];;")
  f.close()
