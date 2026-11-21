import ToyTailCall.SpliceBase

/-!
# Proof support: the spliced program of a well-formed call site

`Site` bundles a call site `call g args dst next` at `pc = k` of function `ci` for which
`inlineCallSite .corrected` actually splices, and records the layout facts of the spliced
function `c'` (slots, destructors and code positions).
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall

set_option linter.unusedSimpArgs false

structure Site where
  p : Prog
  ci : Nat
  k : Nat
  c : Fn
  g : FnId
  gf : Fn
  args : List Operand
  dst : Nat
  next : Nat
  hc : p.fns[ci]? = some c
  hk : c.code[k]? = some (.call g args dst next)
  hgci : g ≠ ci
  hg : p.fns[g]? = some gf
  hlen : args.length = gf.nParams
  hpar : gf.nParams ≤ gf.nSlots
  hdst : dst < c.nSlots

namespace Site

variable (S : Site)

def nC : Nat := S.c.nSlots
def nG : Nat := S.gf.nSlots
def nT : Nat := maxTailArity S.gf.code + 1
def L : Nat := S.c.code.length
def gStart : Nat := S.L + 1 + S.args.length
def K : Nat := maxTailArity S.gf.code + 3
def c' : Fn := spliceFn .corrected S.c S.gf S.k S.args S.dst S.next
def p' : Prog := ⟨S.p.fns.set S.ci S.c'⟩

/-- The function run by a frame of the spliced program, given the original one. -/
def fnS (f : FnId) (fn : Fn) : Fn := if f = S.ci then S.c' else fn

theorem inline_eq : inlineCallSite .corrected S.p S.ci S.k = S.p' := by
  unfold inlineCallSite
  rw [S.hc]
  simp only
  rw [S.hk]
  simp only [S.hgci, ↓reduceIte, S.hg]
  have hcond : S.args.length = S.gf.nParams ∧ S.gf.nParams ≤ S.gf.nSlots ∧ S.dst < S.c.nSlots :=
    ⟨S.hlen, S.hpar, S.hdst⟩
  simp only [hcond, and_self, ↓reduceIte]
  rfl

theorem ci_lt : S.ci < S.p.fns.length := by
  have := S.hc
  rw [List.getElem?_eq_some_iff] at this
  exact this.1

theorem p'_ci : S.p'.fns[S.ci]? = some S.c' := by
  simp only [p', List.getElem?_set_self S.ci_lt]

theorem p'_ne {f : FnId} (h : f ≠ S.ci) : S.p'.fns[f]? = S.p.fns[f]? := by
  simp only [p']
  rw [List.getElem?_set_ne (Ne.symm h)]

theorem p'_fns {f : FnId} {fn : Fn} (h : S.p.fns[f]? = some fn) :
    S.p'.fns[f]? = some (S.fnS f fn) := by
  by_cases hf : f = S.ci
  · subst hf; simp only [fnS, ↓reduceIte, p'_ci]
  · simp only [fnS, hf, ↓reduceIte, p'_ne S hf, h]

theorem fn_ci {fn : Fn} (h : S.p.fns[S.ci]? = some fn) : fn = S.c := by
  rw [S.hc] at h; exact (Option.some.inj h).symm

theorem c'_nParams : S.c'.nParams = S.c.nParams := rfl

theorem c'_dtors : S.c'.dtors = S.c.dtors ++ S.gf.dtors ++ List.replicate S.nT .none := rfl

theorem c'_nSlots : S.c'.nSlots = S.nC + S.nG + S.nT := by
  simp [Fn.nSlots, c'_dtors, nC, nG, Nat.add_assoc]

theorem c'_dtor_c {s : Nat} (h : s < S.nC) : S.c'.dtor s = S.c.dtor s := by
  simp only [Fn.dtor, c'_dtors, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simpa [nC, Fn.nSlots] using h)]

theorem c'_dtor_g {s : Nat} (h : s < S.nG) : S.c'.dtor (s + S.nC) = S.gf.dtor s := by
  simp only [Fn.dtor, c'_dtors, List.getD_eq_getElem?_getD, List.append_assoc]
  have h1 : S.c.dtors.length = S.nC := rfl
  rw [List.getElem?_append_right (by omega), show s + S.nC - S.c.dtors.length = s by omega]
  rw [List.getElem?_append_left (by simpa [nG, Fn.nSlots] using h)]

theorem c'_dtor_hi {s : Nat} (h : S.nC + S.nG ≤ s) : S.c'.dtor s = .none := by
  simp only [Fn.dtor, c'_dtors, List.getD_eq_getElem?_getD]
  have h1 : (S.c.dtors ++ S.gf.dtors).length = S.nC + S.nG := by simp [nC, nG, Fn.nSlots]
  rw [List.getElem?_append_right (by omega)]
  cases hx : (List.replicate S.nT DtorKind.none)[s - (S.c.dtors ++ S.gf.dtors).length]? with
  | none => rfl
  | some x =>
    have := List.mem_of_getElem? hx
    simp [List.eq_of_mem_replicate this]

theorem fnS_nParams {f : FnId} {fn : Fn} (h : S.p.fns[f]? = some fn) :
    (S.fnS f fn).nParams = fn.nParams := by
  unfold fnS; split
  · next hf => subst hf; rw [S.fn_ci h]; rfl
  · rfl

theorem fnS_nSlots_ge {f : FnId} {fn : Fn} (h : S.p.fns[f]? = some fn) :
    fn.nSlots ≤ (S.fnS f fn).nSlots := by
  unfold fnS; split
  · next hf => subst hf; rw [S.fn_ci h, c'_nSlots]; simp [nC]; omega
  · exact Nat.le_refl _

theorem fnS_dtor {f : FnId} {fn : Fn} (h : S.p.fns[f]? = some fn) {s : Nat} (hs : s < fn.nSlots) :
    (S.fnS f fn).dtor s = fn.dtor s := by
  unfold fnS; split
  · next hf => subst hf; rw [S.fn_ci h] at hs ⊢; exact S.c'_dtor_c hs
  · rfl

/-! ### Code layout -/

theorem assignTemps_length (off t base : Nat) :
    ∀ (i : Nat) (as : List Operand), (assignTemps off t base i as).length = as.length
  | _, [] => rfl
  | i, _ :: as => by simp [assignTemps, assignTemps_length off t base (i + 1) as]

theorem assignTemps_getElem? (off t base : Nat) :
    ∀ (as : List Operand) (i j : Nat), (assignTemps off t base i as)[j]? =
      as[j]?.map fun a => Instr.assign (t + (i + j)) (renOp off a) (base + (i + j) + 1)
  | [], _, _ => rfl
  | a :: as, i, 0 => by simp [assignTemps]
  | a :: as, i, j + 1 => by
    simp only [assignTemps, List.getElem?_cons_succ]
    rw [assignTemps_getElem? off t base as (i + 1) j]
    simp only [show i + 1 + j = i + (j + 1) by omega]

theorem padBlock_length {K : Nat} {l : List Instr} (h : l.length ≤ K) :
    (padBlock K l).length = K := by
  simp [padBlock]; omega

theorem padBlock_getElem? {K : Nat} {l : List Instr} {r : Nat} (h : r < l.length) :
    (padBlock K l)[r]? = l[r]? := by
  simp only [padBlock]
  rw [List.getElem?_append_left h]

theorem spliceBody_getElem? (mode : SpliceMode) (nC nG gStart K dst next : Nat) :
    ∀ (code : List Instr) (q0 q : Nat) (i : Instr) (r : Nat),
      (∀ q' i', i' ∈ code → (spliceInstr mode nC nG gStart K dst next q' i').length ≤ K) →
      code[q]? = some i → r < (spliceInstr mode nC nG gStart K dst next (q0 + q) i).length →
      (spliceBody mode nC nG gStart K dst next q0 code)[K * q + r]? =
        (spliceInstr mode nC nG gStart K dst next (q0 + q) i)[r]?
  | [], _, _, _, _, _, h, _ => by simp at h
  | i0 :: code, q0, 0, i, r, hfit, hq, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
    subst hq
    simp only [spliceBody, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hr ⊢
    have hlen := hfit q0 i0 (List.mem_cons_self ..)
    rw [List.getElem?_append_left (by rw [padBlock_length hlen]; omega), padBlock_getElem? hr]
  | i0 :: code, q0, q + 1, i, r, hfit, hq, hr => by
    simp only [List.getElem?_cons_succ] at hq
    simp only [spliceBody]
    have hlen := hfit q0 i0 (List.mem_cons_self ..)
    rw [List.getElem?_append_right (by rw [padBlock_length hlen]; rw [Nat.mul_succ]; omega),
      padBlock_length hlen, show K * (q + 1) + r - K = K * q + r by rw [Nat.mul_succ]; omega]
    have := spliceBody_getElem? mode nC nG gStart K dst next code (q0 + 1) q i r
      (fun q' i' hi => hfit q' i' (List.mem_cons_of_mem _ hi)) hq
      (by rw [show q0 + 1 + q = q0 + (q + 1) by omega]; exact hr)
    rw [this, show q0 + 1 + q = q0 + (q + 1) by omega]

theorem maxTailArity_ge :
    ∀ (code : List Instr) (h : FnId) (as : List Operand), .tailCall h as ∈ code →
      as.length ≤ maxTailArity code
  | [], _, _, hm => by simp at hm
  | i :: code, h, as, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [maxTailArity]; exact Nat.le_max_left _ _
    · have := maxTailArity_ge code h as hm
      cases i <;> simp [maxTailArity] <;> omega

theorem block_fit (q : Nat) (i : Instr) (hi : i ∈ S.gf.code) :
    (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next q i).length ≤ S.K := by
  cases i with
  | tailCall h as =>
    have := maxTailArity_ge S.gf.code h as hi
    simp [spliceInstr, assignTemps_length, K]; omega
  | ret op => simp [spliceInstr, K]
  | _ => simp [spliceInstr, K]

theorem c'_code : S.c'.code = S.c.code.set S.k (.goto S.L) ++
    (.reset ((List.range (S.nG + S.nT)).map (· + S.nC)) (S.L + 1) ::
      assignTemps 0 S.nC (S.L + 1) 0 S.args) ++
    spliceBody .corrected S.nC S.nG S.gStart S.K S.dst S.next 0 S.gf.code := rfl

theorem k_lt : S.k < S.L := by
  have := S.hk
  rw [List.getElem?_eq_some_iff] at this
  exact this.1

theorem code_lt {pc : Nat} (h : pc < S.L) (hk : pc ≠ S.k) : S.c'.code[pc]? = S.c.code[pc]? := by
  rw [c'_code, List.append_assoc, List.getElem?_append_left (by simpa [L] using h),
    List.getElem?_set_ne (Ne.symm hk)]

theorem code_k : S.c'.code[S.k]? = some (.goto S.L) := by
  rw [c'_code, List.append_assoc, List.getElem?_append_left (by simpa [L] using S.k_lt),
    List.getElem?_set_self (by simpa [L] using S.k_lt)]

theorem code_L : S.c'.code[S.L]? =
    some (.reset ((List.range (S.nG + S.nT)).map (· + S.nC)) (S.L + 1)) := by
  rw [c'_code, List.append_assoc, List.getElem?_append_right (by simp [L])]
  simp [L]

theorem code_pro {j : Nat} (hj : j < S.args.length) :
    S.c'.code[S.L + 1 + j]? =
      some (.assign (S.nC + (0 + j)) (renOp 0 S.args[j]) (S.L + 1 + (0 + j) + 1)) := by
  rw [c'_code, List.append_assoc, List.getElem?_append_right (by simp [L]; omega)]
  simp only [List.length_set, show S.L + 1 + j - S.c.code.length = j + 1 by simp [L]; omega,
    List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [assignTemps_length]; exact hj), assignTemps_getElem?]
  simp [List.getElem?_eq_getElem hj]

theorem code_body {q : Nat} {i : Instr} (hq : S.gf.code[q]? = some i) {r : Nat}
    (hr : r < (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next q i).length) :
    S.c'.code[S.gStart + S.K * q + r]? =
      (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next q i)[r]? := by
  rw [c'_code, List.getElem?_append_right (by simp [gStart, L, assignTemps_length]; omega)]
  have hl : (S.c.code.set S.k (.goto S.L) ++
      (.reset ((List.range (S.nG + S.nT)).map (· + S.nC)) (S.L + 1) ::
        assignTemps 0 S.nC (S.L + 1) 0 S.args)).length = S.gStart := by
    simp [gStart, L, assignTemps_length]; omega
  rw [hl, show S.gStart + S.K * q + r - S.gStart = S.K * q + r by omega]
  have := spliceBody_getElem? .corrected S.nC S.nG S.gStart S.K S.dst S.next S.gf.code 0 q i r
    (fun q' i' hi => S.block_fit q' i' hi) hq (by rw [Nat.zero_add]; exact hr)
  rw [this, Nat.zero_add]

end Site

end Toy.TailCall.SpliceProof
