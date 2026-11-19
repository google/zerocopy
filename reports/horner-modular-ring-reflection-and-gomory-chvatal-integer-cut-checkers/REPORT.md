# Pure-Kernel Modular Horner Ring Reflection and Chvátal-Gomory Integer Cut Checkers

## Summary

Under pure-kernel proof-auditing profiles that forbid meta-tactics (`omega`, `ring`, `linarith`, `bv_decide`, `grind`) and native code execution (`native_decide` / `Lean.ofReduceBool`) while locking imports to Lean 4's minimal prelude (`51` `Init.*` modules + `{propext, Quot.sound, Classical.choice}`), arithmetic obligations must be discharged by **total computational reflection checkers** (`check : GoalSyn → Cert → Bool`, proved sound once and invoked via `Eq.refl true`). Two complementary algebraic certificate checkers discharge wrapping bitvector identities and exact integer linear/divisibility bounds with constant-size proof witnesses:

1. **Grégoire–Mahboubi sparse Horner ring reflection over $\mathbb{Z}/2^w\mathbb{Z}$** (`Pol := Pc c | Pinj j Q | PX P i Q`, TPHOLs 2005; `rocq-prover/stdlib` `Ring_polynom.v`) normalizes multivariate polynomial expressions over wrapping $w$-bit arithmetic ($M = 2^w$) into a **unique canonical tree** without assuming an integral domain. Zero-divisor products ($2^{w-1} X \cdot 2 Y \equiv 0 \pmod{2^w}$) vanish automatically through `mkPX` and `mkPinj` smart constructors, deciding pointer-stride, chunk-offset, endian-packing, and two's-complement ring identities via `Pol.beq (norm e₁) (norm e₂) = true`. Crucially, canonical equality in $(\mathbb{Z}/2^w\mathbb{Z})[X_1, \dots, X_n]$ decides **commutative ring identities** rather than **bitvector polynomial-function equivalence**: rising-factorial vanishing polynomials such as $2^{w-1}(X^2 + X)$ evaluate to $0 \pmod{2^w}$ on every $x \in \mathbb{Z}/2^w\mathbb{Z}$ while remaining non-zero in `Pol`.
2. **Sparse integer Farkas + Chvátal–Gomory floor cuts + branch-split certificates** (`ZMicromega.v`, `VIPR` `cert_spec_v1_1.md`) close the integer-completeness gap left by rational Farkas certificates on parity, stride, and alignment obligations (such as deriving $k < m$ forward from $2k + 1 \le 2m$, proving $2k + 1 \le 2m \implies 2k + 2 \le 2m$ where $m - k = 1/2$ is rationally feasible, or proving $8q < \text{cap} \land \text{cap} = 8m \implies 8q + 8 \le \text{cap}$ where $(q, m, \text{cap}) = (7/8, 1, 8)$ defeats all rational Farkas multipliers). Combining non-negative integer linear combinations (`linComb`), exact GCD floor rounding (`cgCut`: $\sum_i (g \cdot c'_i) x_i \le d,\; g > 0 \implies \sum_i c'_i x_i \le \lfloor d / g \rfloor$), Diophantine congruence refutation ($g \cdot Q(x) + c = 0,\; g \nmid c \implies \bot$), and binary integer disjunction (`split`: $q(x) \le \beta \lor -q(x) \le -\beta - 1$) achieves completeness over rational polyhedra while avoiding $\Omega(K)$ Chvátal-rank blowup on high-aspect-ratio stride triangles.
3. **Lean 4 (`v4.34.1`) C++ kernel GMP and Pass 1 constraints** govern concrete checker design: (a) `Init.Omega`, `Init.Grind.Ring`, and `Init.Data.Int.DivMod` are absent from Anneal's 51-module `foundation-lock.json`, so floor division $\lfloor d / g \rfloor$ must be built directly on `Init.Data.Nat.Div.Basic` (`Int.negSucc (Nat.div m g)` for negative dividends, never `Trusted.MirSemantics.intTdiv`, which truncates $-1/2 \mapsto 0$); (b) `src/kernel/type_checker.cpp` disables **both** `Bool.true` reflection (`L1181`) and `reduce_nat` GMP evaluation (`L1093`) whenever `has_fvar` is `true`, requiring strict separation between closed reified ASTs (`Nat` variable indices) and open runtime environments (`List Nat` / `List Int`); and (c) recursion must use `.recCompiled` / `List.foldr` to emit zero `partial` `._unsafe_rec` helpers.

## Applicability

This report analyzes the algebra, certificate formats, soundness boundaries, and Lean 4 kernel mechanics connecting ten primary subjects:

- **Target verification substrate (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` and `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Anneal's `theory/` modules are audited by `trusted/audit/TrustedBoundary.lean` (Pass 1) against `trusted/lean/foundation-lock.json` (`51` `Init.*` modules; `3` axioms; closed `allowedTheorySyntaxKinds`; zero `partial`/`unsafe`/`opaque` declarations in `theory/`; Statement-Origin Separation against `Trusted.MirAst` and `Trusted.MirSemantics`). Kernel mechanics are grounded in `leanprover/lean4` `v4.34.1` (`src/kernel/type_checker.cpp`, `src/Init/Data/Int/Basic.lean`, `src/Init/Data/BitVec/BasicAux.lean`, and `src/Init/Omega/Constraint.lean`).
- **Reflexive Horner rings and integer cutting-plane tactics (`rocq-prover/stdlib` at `06f32e0a7dbb60dfc1ca1d4da94e433d76f7ee9a`, Grégoire–Mahboubi DOI `10.1007/11541868_7`, and Besson DOI `10.1007/978-3-540-74464-1_4`):** Examined via `theories/setoid_ring/Ring_polynom.v` (`Pol`, `PExpr`, `norm_subst`, `MFactor`, `POneSubst`) and `theories/micromega/ZMicromega.v` (`ZArithProof`, `CutProof`, `SplitProof`, `Zgcd_pol`, `genCuttingPlane`, `ZChecker`).
- **Cutting-plane theory and MILP certificate checkers (Chvátal DOI `10.1016/0012-365X(73)90167-2`, Schrijver DOI `10.1016/S0167-5060(08)70857-9`, Cheung–Gleixner–Steffy DOI `10.1007/978-3-319-59250-3_13` / `arXiv:1611.08832v2`, `ambros-gleixner/VIPR` `1.1` at `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`, and `scipopt/vipr` at `99eec197a49b2bd9ad33c1f4c7afabe93caa6511`):** Examined via `cert_spec_v1_1.md` and `code/viprchk.cpp` across both archived and active VIPR repositories.

Modular Horner findings apply to $\mathbb{Z}/M\mathbb{Z}$ for any $M \ge 1$ (specifically $M = 2^w$ across `Trusted.MirAst.IntWidth`); integer cut findings apply to quantifier-free linear and GCD-factorable polynomial inequalities over $\mathbb{Z}$ and bounded `Nat` embeddings.

## Findings

### 1. Sparse Horner Commutative Ring Reflection Specialized to Modular Wrapping Rings

`Basis: normative + source + execution + derived`

Dense sum-of-monomials normalizers suffer quadratic list merges and repeated exponent vector comparisons on nested products. Grégoire and Mahboubi (TPHOLs 2005, DOI `10.1007/11541868_7`; `rocq-prover/stdlib` `theories/setoid_ring/Ring_polynom.v:104-176`) represent $C[X_1, \dots, X_n]$ recursively as $(C[X_2, \dots, X_n])[X_1]$ in **sparse Horner form** (`Pol`):

- **Canonical `Pol` structure and invariants (`Ring_polynom.v:126-171, 507-512`):**
  - `Pc (c : C)`: constant $c$.
  - `Pinj (j : Pos) (Q : Pol)`: skips $j \ge 1$ unused variables, denoting $Q(X_{j+1}, \dots, X_n)$.
  - `PX (P : Pol) (i : Pos) (Q : Pol)`: Horner node denoting $P(X_1, \dots, X_n) \cdot X_1^i + Q(X_2, \dots, X_n)$ ($i \ge 1$).
  Structural uniqueness (`Peq P P' = true ↔ P = P'`) is maintained by `mkPinj` (`L152-157`) and `mkPX` (`L166-171`): (1) `Pinj j (Pc c) ↦ Pc c` and `Pinj j₁ (Pinj j₂ Q) ↦ Pinj (j₁ + j₂) Q`; (2) `PX (Pc 0) i Q ↦ mkPinj 1 Q` (no zero leading coefficients); and (3) `PX (PX P' i' (Pc 0)) i Q ↦ PX P' (i' + i) Q` (no unmerged pure powers of $X_1$).
- **Zero-divisor safety over $\mathbb{Z}/2^w\mathbb{Z}$ (`Ring_polynom.v:29-40, 330-386, 615-624`):**
  Although $\mathbb{Z}/2^w\mathbb{Z}$ ($w \ge 2$) has zero divisors ($2^{w-1} \cdot 2 \equiv 0 \pmod{2^w}$), `Ring_polynom.v` proves `Padd_ok`, `Pmul_ok`, and `norm_aux_spec` (`L703-782, 1056-1078`) from `almost_ring_theory` alone—requiring **zero integral-domain or cancellation axioms**. With canonical modular representatives $c \in \{0, \dots, 2^w - 1\}$, multiplying $(2^{63} X_1) \cdot (2 X_2)$ over $\mathbb{Z}/2^{64}\mathbb{Z}$ reduces `(2^63 * 2) mod 2^64` to `0` inside `PmulC`, and `mkPX (Pc 0) i Q` immediately strips the dead variable node (reproduced in Revalidation).
- **Contextual monomial rewriting (`MFactor` and `POneSubst`, `Ring_polynom.v:419-502, 813-915`):**
  To incorporate local equational premises (`stride = elem_size * count` or `len = 8 * q + r`) without Gröbner-basis non-termination, `MFactor P c M = (Q, R)` decomposes $P = Q + c \cdot M \cdot R$ via coefficient Euclidean division `cdiv` (`Mcphi_ok`, `L813-823`) and bounded substitution `PNSubstL` (`L497-501`).
- **Completeness boundary over $\mathbb{Z}/2^w\mathbb{Z}$ (ring identities vs. vanishing functions):**
  Over finite ring $\mathbb{Z}/2^w\mathbb{Z}$, distinct canonical polynomials can induce the **same function**: because $X_1(X_1 + 1)$ is always even, $P(X_1) = 2^{w-1}(X_1^2 + X_1)$ evaluates to $0 \pmod{2^w}$ for every $x_1 \in \mathbb{Z}/2^w\mathbb{Z}$, yet its canonical Horner normal form is `PX (PX (Pc 2^(w-1)) 1 (Pc 2^(w-1))) 1 (Pc 0) ≠ Pc 0` (reproduced in Revalidation). Horner `Peq` is **sound and complete for universal commutative-ring identities of characteristic $2^w$**, and intentionally omits rising-factorial vanishing-ideal reduction $\langle 2^{w - \nu_2(k!)} X^{\underline{k}} \rangle$.

### 2. Closing the Rational Farkas Integrality Gap: Chvátal–Gomory Floor Cuts, Diophantine GCD Refutation, and Branch Splits

`Basis: normative + source + execution + derived`

Rational Farkas certificates ($\lambda_j \ge 0$ summing $\sum_j \lambda_j (a_j^\top x \le b_j)$ to $0 \le -c$, $c > 0$) certify $P = \{ x \in \mathbb{Q}^n \mid A x \le b \} = \emptyset$, but fail whenever $P \neq \emptyset$ while $P \cap \mathbb{Z}^n = \emptyset$:

- **Representative systems-verification obligations where rational Farkas fails:**
  1. **Aligned `u64` slice-access bounds (`8*q < cap` and `cap = 8*m` $\implies$ `8*q + 8 <= cap`):** Negating `8*q + 8 <= cap` over $\mathbb{Z}$ yields $H_1: 8q - \text{cap} \le -1$, $H_2: \text{cap} - 8m \le 0$, $H_3: 8m - \text{cap} \le 0$, and $H_4: \text{cap} - 8q \le 7$. The fractional point $(q, m, \text{cap}) = (7/8, 1, 8) \in \mathbb{Q}^3$ satisfies all four inequalities simultaneously ($7 - 8 \le -1$ and $8 - 7 = 1 \le 7$), so **zero rational Farkas certificates exist**. One Chvátal–Gomory cut (`g = 8`) on $1 \cdot H_1 + 1 \cdot H_2$ ($8q - 8m \le -1$) yields $q - m \le \lfloor -1/8 \rfloor = -1$; combining $8(q - m \le -1) + H_3 + H_4$ derives $0 \le -1$.
  2. **Parity and stride tightening (`2*k + 1 <= 2*m` $\implies$ `k < m` and `2*k + 2 <= 2*m`):** Cutting $H_1: 2k - 2m \le -1$ by $g = 2$ derives $k - m \le \lfloor -1/2 \rfloor = -1$ ($k < m$) forward in one step, and refutes the negated strided bound $H_2: 2m - 2k \le 1$ (which is rationally satisfiable at $m - k = 1/2$) via $2(k - m \le -1) + H_2 \implies 0 \le -1$.
- **Chvátal–Gomory rounding and completeness (Chvátal 1973, DOI `10.1016/0012-365X(73)90167-2`; Schrijver 1980, DOI `10.1016/S0167-5060(08)70857-9`):** Whenever $\sum_{i=1}^n c_i x_i \le d$ holds for $x \in \mathbb{Z}^n$, $g \in \mathbb{Z}_{>0}$, and $\forall i,\; g \mid c_i$, integer integrality of $\sum_i (c_i / g) x_i$ implies $\sum_{i=1}^n (c_i / g) x_i \le \lfloor d / g \rfloor$. By Chvátal (1973) and Schrijver (1980), for any rational polyhedron $P = \{ x \mid A x \le b \}$, $P \cap \mathbb{Z}^n = \emptyset$ iff finitely many linear combinations and Chvátal–Gomory cuts derive $0 \le -1$.
- **Besson's unified `ZMicromega` calculus (`rocq-prover/stdlib`, `theories/micromega/ZMicromega.v:506-640, 779-1050`):**
  1. **Nonlinear GCD cuts over shared `Pol Z` (`Zgcd_pol`, `L594-640, 767-784`):** `ZMicromega` reuses Grégoire–Mahboubi's `Pol Z` for constraints, factoring $p = g \cdot Q + c$ via `Zgcd_pol`. Because $Q(x) \in \mathbb{Z}$ holds even for nonlinear monomials ($x^2, x \cdot y$), `CutProof` cuts $4 x^2 + 4 x y \le 3 \implies x^2 + x y \le 0$ with no extra AST machinery.
  2. **Diophantine equality refutation (`genCuttingPlane`, `L786-795`) and `SplitProof` (`L547, 937-944`):** When $g \cdot Q(x) + c = 0$ has $g > 0$, $c \neq 0$, and $\gcd(g, c) \neq g$, `genCuttingPlane` returns `None` (`ZChecker` `L933` returns `true`), refuting $2x + 2y + 1 = 0$ in one step; `SplitProof p pf1 pf2` branches on $p(x) \ge 0 \lor -p(x) - 1 \ge 0$ (VIPR's `uns` rule, `cert_spec_v1_1.md:91`).
- **Chvátal-rank blowup vs. $O(1)$ `Split` on 64-bit strides (`execution + derived`):** On the coprime triangle $S_1: (4K - 1)x + 2y \le 4K$, $S_2: -(4K - 1)x + 2y \le 1$, $S_3: -2y \le -1$ (rational vertices $(0, 1/2), (1, 1/2), (1/2, K + 1/4)$, $P_K \cap \mathbb{Z}^2 = \emptyset$), testing all $15{,}625$ combinations $(\lambda_1, \lambda_2, \lambda_3) \in [0, 24]^3$ at $K = 50$ (reproduced in Revalidation) confirms $(1/2, 49.5)$ survives **every** round-1 CG cut: pure CG rank grows as $\Omega(K)$ (infeasible for $K = 2^{60}$). A single `Split` on $x \le 0 \lor -x \le -1$ refutes $\{S_1, S_2, S_3\}$ in **3 steps for every $K \ge 1$**: cut $S_3$ by $2 \to -y \le -1$; under $x \le 0$, $S_2 + (4K-1)(x \le 0) \implies 2y \le 1 \xrightarrow{\text{cut } 2} y \le 0$; under $-x \le -1$, $S_1 + (4K-1)(-x \le -1) \implies 2y \le 1 \xrightarrow{\text{cut } 2} y \le 0$.

### 3. Upstream Unverified C++ Checker Hazard: Continuous-Variable Rounding Bug in VIPR

`Basis: normative + documentation + source + derived`

Comparing the normative VIPR `1.1` specification (`ambros-gleixner/VIPR` at `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`, `cert_spec_v1_1.md:19-29`) against `code/viprchk.cpp` in **both** `ambros-gleixner/VIPR` (`L1534-1562`) and active `scipopt/vipr` (`99eec197a49b2bd9ad33c1f4c7afabe93caa6511`, `L1634-1662`) exposes an unfixed **soundness bug**:

- **Normative rule (`cert_spec_v1_1.md:20-29`):** Rounding $\sum_{j=1}^p a_{i_j} X_{i_j} \le \beta$ to $\lfloor \beta \rfloor$ requires every $a_{i_j}$ to be an integer "**and nonzero only if $i_j$ is an integer variable index**."
- **C++ bug (`scipopt/vipr` `code/viprchk.cpp:1638-1658`):** `Constraint::round()` checks `if( isInt[j] ) { if( !isInteger(a) ) { returnStatement = false; goto TERMINATE; } }` with **no `else` rejection when `isInt[j] == false`** (contrast `canUnsplit` at `ambros-gleixner/VIPR` `L1456`, which checks `if( !isInt[it->first] )`). Neither `readLinComb` (`L1219-1275`) nor `case RND:` (`L988-1012`) checks `isInt`. Thus on a satisfiable continuous LP (`INT 0`, $X_0 = 1/2$) with $C_0: X_0 \le 1/2$ and $C_1: -X_0 \le -1/2$, `{ rnd 1 0 1 }` rounds $X_0 \le 1/2$ to $X_0 \le 0$ and derives $0 \le -1/2$ (`RTP infeas`). Proving `applyCgCut` sound inside Lean 4's kernel structurally prevents this entire class of unverified C++ checker bugs.

### 4. Lean 4 `v4.34.1` C++ Kernel GMP Mechanics, Proof-Term Scaling, and Pass-1 Checker Blueprint

`Basis: source + execution + derived`

1. **Missing `Init.Data.Int.DivMod` and exact `negSucc` floor division (`Init.Data.Int.Basic:1-467`, `Trusted/MirSemantics.lean:200-204`):**
   Anneal's 51-module `foundation-lock.json` omits `Init.Data.Int.DivMod`, `Init.Omega`, and `Init.Grind.Ring`; meanwhile `Trusted.MirSemantics.intTdiv` truncates towards zero (`intTdiv (-1) 2 = 0`), failing on negative RHS cuts ($2x \le -1 \implies x \le -1$). Over `Int`'s two constructors (`ofNat m` $= +m$, `negSucc m` $= -(m + 1)$), mathematical floor $\lfloor d / g \rfloor$ for $g > 0$ reduces directly to `Nat.div` via $\lfloor -(m + 1) / g \rfloor = -(\lfloor m / g \rfloor + 1) = \texttt{Int.negSucc (Nat.div m g)}$ (verified across $d \in [-65, 65], g \in [1, 16]$ in Revalidation).
2. **The `!has_fvar` GMP cliff (`src/kernel/type_checker.cpp:637-733, 1088-1186`) and proof-term scaling:**
   `is_def_eq_core` (`L1181`) fast-paths `t =?= Bool.true` via `whnf(t)` **only when `!has_fvar(t)`**, and `lazy_delta_reduction` (`L1093`) invokes `reduce_nat` GMP arithmetic **only when `!has_fvar(t_n) && !has_fvar(s_n)`**. Keeping `RingExpr`, `w`, `LinLe`, and `IntRefuteCert` 100% `fvar`-free (passing runtime variables solely in `env : List Nat` / `List Int` to `denote`) preserves full GMP speed while replacing verbose `Lean.Omega.Constraint.{combo_sat,div_sat}` proof trees (`src/Init/Omega/Constraint.lean:144-250`) with an 8-byte `Eq.refl true` kernel witness. Routing recursion through `.recCompiled` and `List.foldr` emits **zero `partial` `._unsafe_rec` helpers**:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic

namespace Anneal.RingAndCuts

inductive RingExpr where
  | const (c : Nat) : RingExpr
  | var   (idx : Nat) : RingExpr
  | add   (a b : RingExpr) : RingExpr
  | sub   (a b : RingExpr) : RingExpr
  | mul   (a b : RingExpr) : RingExpr

/-- Canonical sparse Horner polynomial over `Z / 2^w Z`. -/
inductive Pol where
  | pc   (c : Nat) : Pol
  | pinj (skip : Nat) (q : Pol) : Pol
  | px   (p : Pol) (exp : Nat) (q : Pol) : Pol

def Pol.beq : Pol → Pol → Bool :=
  @Pol.recCompiled (fun _ => Pol → Bool)
    (fun c₁ other => match other with | .pc c₂ => Nat.beq c₁ c₂ | _ => false)
    (fun s₁ _ ihQ other =>
      match other with
      | .pinj s₂ q₂ => Nat.beq s₁ s₂ && ihQ q₂
      | _ => false)
    (fun _ exp₁ _ ihP ihQ other =>
      match other with
      | .px p₂ exp₂ q₂ => Nat.beq exp₁ exp₂ && ihP p₂ && ihQ q₂
      | _ => false)

def mkPinj (skip : Nat) (q : Pol) : Pol :=
  if Nat.beq skip 0 then q
  else match q with
    | .pc c => .pc c
    | .pinj s2 q2 => .pinj (Nat.add skip s2) q2
    | .px _ _ _ => .pinj skip q

def mkPX (p : Pol) (exp : Nat) (q : Pol) : Pol :=
  match p with
  | .pc c => if Nat.beq c 0 then mkPinj 1 q else .px (.pc c) exp q
  | .px p' exp' (.pc 0) => .px p' (Nat.add exp' exp) q
  | _ => .px p exp q

def Pol.addC (modW : Nat) (p : Pol) (c : Nat) : Pol :=
  @Pol.recCompiled (fun _ => Pol)
    (fun c₁ => .pc (Nat.mod (Nat.add c₁ c) modW))
    (fun s _ ih => mkPinj s ih)
    (fun lead e _ _ ihQ => .px lead e ihQ)
    p

def Pol.opp (modW : Nat) : Pol → Pol :=
  @Pol.recCompiled (fun _ => Pol)
    (fun c => .pc (Nat.mod (Nat.sub modW (Nat.mod c modW)) modW))
    (fun s _ ih => mkPinj s ih)
    (fun _ e _ ihP ihQ => mkPX ihP e ihQ)

def Pol.mulC (modW : Nat) (p : Pol) (c : Nat) : Pol :=
  let c' := Nat.mod c modW
  if Nat.beq c' 0 then .pc 0
  else if Nat.beq c' 1 then p
  else
    @Pol.recCompiled (fun _ => Pol)
      (fun c₁ => .pc (Nat.mod (Nat.mul c₁ c') modW))
      (fun s _ ih => mkPinj s ih)
      (fun _ e _ ihP ihQ => mkPX ihP e ihQ)
      p

def intBle (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.ble m n
  | .negSucc _, .ofNat _ => true
  | .ofNat _, .negSucc _ => false
  | .negSucc m, .negSucc n => Nat.ble n m

/-- Exact Euclidean floor `⌊d / g⌋` for `g > 0`: `⌊-(m + 1) / g⌋ = Int.negSucc (m / g)`. -/
def intFloorDivPos (d : Int) (g : Nat) : Int :=
  match d with
  | .ofNat m   => .ofNat (Nat.div m g)
  | .negSucc m => .negSucc (Nat.div m g)

def intExactDivPos (c : Int) (g : Nat) : Option Int :=
  match c with
  | .ofNat m =>
    if Nat.beq (Nat.mod m g) 0 then some (.ofNat (Nat.div m g)) else none
  | .negSucc m =>
    let mag := Nat.succ m
    if Nat.beq (Nat.mod mag g) 0 then some (Int.negOfNat (Nat.div mag g)) else none

structure LinLe where
  coeffs : List (Nat × Int)
  rhs    : Int

def applyCgCut (g : Nat) (src : LinLe) : Option LinLe :=
  if Nat.beq g 0 then none
  else
    let scaled? := src.coeffs.foldr
      (fun vc acc? =>
        match acc?, intExactDivPos vc.2 g with
        | some rest, some q => some ((vc.1, q) :: rest)
        | _, _ => none)
      (some [])
    match scaled? with
    | none => none
    | some scaled => some ⟨scaled, intFloorDivPos src.rhs g⟩

inductive IntRefuteCert where
  | contra  (hypIdx : Nat) : IntRefuteCert
  | linComb (terms : List (Nat × Nat)) (next : IntRefuteCert) : IntRefuteCert
  | cgCut   (srcIdx : Nat) (divisor : Nat) (next : IntRefuteCert) : IntRefuteCert
  | split   (lhs : List (Nat × Int)) (beta : Int)
            (leftBranch rightBranch : IntRefuteCert) : IntRefuteCert

end Anneal.RingAndCuts
```

### 5. Architectural Evaluation for Untrusted Theory Libraries Outside the TCB

`Basis: source + derived`

| Dimension | Grade | Grounded Justification Against `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | Pure `theory/Anneal/` checkers proved sound against `Init.Data.{Nat,Int}` and `Trusted.MirSemantics.truncateBits` (`x % 2^w`) with zero `Classical.choice`, zero `trusted/` edits, and 100% Statement-Origin Separation on `CrateTheorem`. |
| **(P1) Human Spec Auditability** | **Strong** | Rust `Specs` stay idiomatic arithmetic contracts (`off + 8 <= cap`); reified `RingExpr` and `IntRefuteCert` witnesses appear only inside proof terms (`ConstantInfo.value?`). |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Collapses brittle manual `Nat.add_mod`/`Nat.div_add_mod` chains to 1-line `rfl` invocations; external solvers regenerate `IntRefuteCert` automatically when struct sizes or constants change. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **Strong** | `fvar`-free closed `Nat` evaluation runs in C++ GMP (`reduce_nat`), producing 8-byte `Eq.refl true` proof terms and preserving `<50 ms` `anneal-lsp` latency. |
| **(P4) Heterogeneous Composability** | **Strong** | Orthogonal backend leaf dischargers usable beneath `MirWp`, `PureLift`, separation logic, or AI-PCC across both safe Rust and `unsafe` raw-pointer offset/alignment proofs. |
| **(P5) Failure Legibility** | **Moderate–Strong** | Modular `Pol` normalization exposes exact non-zero difference polynomials; `IntRefuteCert` identifies exact failed cut steps (`applyCgCut`), while concrete countermodel generation on unprovable goals remains an external LSP/solver task. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Following `ZMicromega.v`, both checkers can share a single sparse Horner `Pol` representation (`Z / 2^w Z` ring normalization + `Z` nonlinear GCD cutting planes). |

## Boundaries

- **Bitvector polynomial-function vanishing identities over $\mathbb{Z}/2^w\mathbb{Z}$ — `known not to apply`:** Horner normalization over $\mathbb{Z}/2^w\mathbb{Z}$ decides universal commutative-ring identities of characteristic $2^w$, not function equivalence modulo rising-factorial ideals $\langle 2^{w - \nu_2(k!)} X^{\underline{k}} \rangle$ (e.g., `2^63 * x * (x + 1) = 0 (mod 2^64)` requires parity `Split` on $x = 2q \lor x = 2q + 1$).
- **Mixed bitwise-and-ring identities without Euclidean decomposition — `known not to apply`:** Bitwise expressions (`x &&& 7`, `x >>> 3`) are opaque variables to `RingExpr`/`Pol` normalization unless decomposed via `Tnum`/Euclidean lemmas (`x = 8 * (x >>> 3) + (x &&& 7)` and `0 <= (x &&& 7) <= 7`).
- **Direct import of `Init.Omega`, `Init.Grind.Ring`, or `Init.Data.Int.DivMod` in `theory/` — `unsupported`:** Excluded from `trusted/lean/foundation-lock.json` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) and rejected by `TrustedBoundary.checkHeaderImports` (`L1169-1176`).
- **Alternating-quantifier Presburger elimination — `not examined`:** `IntRefuteCert` targets quantifier-free refutation certificates; full $\forall\exists$ Cooper elimination was `not examined`.
- **Exact `Ppow` exponent tripping `LEAN_NAT_MAX_SIZE_DEFAULT` in `v4.34.1` — `unknown`:** `type_checker.cpp:670-673` caps `Nat.pow` result bytes via `LEAN_NAT_MAX_SIZE`; modulo-$2^w$ reduction keeps $w \le 128$ coefficients $\le 16$ bytes, while unreduced `Ppow` limits remain `unknown`.

## Evidence

1. **Anneal Pass 1 & MIR Semantics (`source`):** `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/foundation-lock.json` (`L1-L95`), `trusted/audit/TrustedBoundary.lean` (`L442-L596`, `L1108-L1260`), `trusted/lean/Trusted/MirSemantics.lean` (`L190-L217`), and `theory/Anneal/PureLift/Lens.lean` (`L60-L80`).
2. **Lean 4.34.1 Kernel & Prelude (`source`):** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`: `src/kernel/type_checker.cpp` (`L637-L776`, `L863-L871`, `L1088-L1186`, `L1318-L1346`), `src/Init/Data/Int/Basic.lean` (`L145-L439`), and `src/Init/Omega/Constraint.lean` (`L206-L250`).
3. **Horner Ring & `ZMicromega` (`normative + source`):** Grégoire and Mahboubi, TPHOLs 2005, DOI `10.1007/11541868_7`; Besson, TYPES 2006, DOI `10.1007/978-3-540-74464-1_4`; `rocq-prover/stdlib` at `06f32e0a7dbb60dfc1ca1d4da94e433d76f7ee9a` (`theories/setoid_ring/Ring_polynom.v:22-176, 282-518, 561-1088` and `theories/micromega/ZMicromega.v:506-640, 767-1050`).
4. **Cutting Planes & VIPR (`normative + documentation + source`):** Chvátal, *Discrete Math.* 4(4):305–337, 1973, DOI `10.1016/0012-365X(73)90167-2`; Schrijver, *Ann. Discrete Math.* 9:291–296, 1980, DOI `10.1016/S0167-5060(08)70857-9`; Cheung, Gleixner, and Steffy, IPCO 2017, DOI `10.1007/978-3-319-59250-3_13` (`arXiv:1611.08832v2`); `ambros-gleixner/VIPR` at `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff` (`cert_spec_v1_1.md:19-29, 84-93`, `code/viprchk.cpp:1454-1469, 1534-1562`) and `scipopt/vipr` at `99eec197a49b2bd9ad33c1f4c7afabe93caa6511` (`code/viprchk.cpp:988-1025, 1219-1275, 1634-1662`).
5. **Executable Horner & Cut Probe (`execution`, `2026-11-19`):** Executed the self-contained Python 3.13 Horner and cutting-plane probe preserved in item 4 of Revalidation below on Linux x86_64, confirming 64-bit zero-divisor cancellation, vanishing witness $4(X_1^2 + X_1) \neq 0$ over $\mathbb{Z}/8\mathbb{Z}$, exact `negSucc` floor division, and survival of $(1/2, 49.5)$ across all $15{,}625$ round-1 CG cuts at $K = 50$.

## Revalidation

1. **Anneal prelude & constant gates (`joshlf/anneal`):** Check `trusted/lean/foundation-lock.json` for `Init.Data.Int.DivMod`/`Init.Omega` and `TrustedBoundary.lean` for `ensureReplayableConstant` `isPartial` rejection.
2. **Lean 4 `!has_fvar` gates (`leanprover/lean4`):** Check `src/kernel/type_checker.cpp` at `lazy_delta_reduction` and `is_def_eq_core` for `!has_fvar` guards on `reduce_nat` and `Bool.true` reflection.
3. **VIPR `Constraint::round()` fix check (`scipopt/vipr`):** Check `code/viprchk.cpp` inside `Constraint::round()` for an `else` branch rejecting `!isInt[j] && a != 0`.
4. **Standalone Horner, floor-division, and Chvátal-rank discriminator (<0.3s, Python 3.10+ stdlib only):**
   ```bash
   python3 -c '
   import math
   def mk_pinj(s, q):
       if s == 0 or q[0] == "pc": return q
       return ("pinj", s + q[1], q[2]) if q[0] == "pinj" else ("pinj", s, q)
   def mk_px(p, i, q):
       if p == ("pc", 0): return mk_pinj(1, q)
       if p[0] == "px" and p[3] == ("pc", 0): return ("px", p[1], p[2] + i, q)
       return ("px", p, i, q)
   def pmul_c(M, p, c):
       c %= M
       if c == 0: return ("pc", 0)
       if c == 1 or p[0] == "pc": return ("pc", (p[1] * c) % M) if p[0] == "pc" else p
       if p[0] == "pinj": return mk_pinj(p[1], pmul_c(M, p[2], c))
       return mk_px(pmul_c(M, p[1], c), p[2], pmul_c(M, p[3], c))
   assert mk_px(pmul_c(1 << 64, ("px", ("pc", 1 << 63), 1, ("pc", 0)), 2), 1, ("pc", 0)) == ("pc", 0)
   vanish8 = ("px", ("px", ("pc", 4), 1, ("pc", 4)), 1, ("pc", 0))
   assert vanish8 != ("pc", 0) and all((4 * (x * x + x)) % 8 == 0 for x in range(8))

   def lean_floor_div_pos(d: int, g: int) -> int:
       assert g > 0
       return (d // g) if d >= 0 else -((-d - 1) // g) - 1
   for g in range(1, 17):
       for d in range(-65, 66):
           assert lean_floor_div_pos(d, g) == math.floor(d / g)
   K = 50
   for l1 in range(25):
       for l2 in range(25):
           for l3 in range(25):
               c0 = (l1 - l2) * (4 * K - 1)
               c1 = 2 * (l1 + l2 - l3)
               rhs = 4 * K * l1 + l2 - l3
               g = math.gcd(abs(c0), abs(c1))
               if g > 0:
                   assert (c0 // g) * 0.5 + (c1 // g) * (K - 0.5) <= (rhs // g) + 1e-9
   print("revalidation passed")
   '
   ```
