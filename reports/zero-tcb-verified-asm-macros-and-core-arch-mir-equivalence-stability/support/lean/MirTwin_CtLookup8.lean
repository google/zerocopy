-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Omega
import AsmMirBase

namespace LockedObligations

open AsmMirBase

theorem verify_ct_lookup8_mir_twin (s : X86State) (base idx : Nat) :
    ctSelectMirTwin s base (idx % W64) = lookup8Spec s base (idx % W64) := by
  unfold ctSelectMirTwin lookup8Spec ctSelectStep
  generalize hk : idx % W64 = k
  by_cases h7 : k = 7
  · subst h7; simp
  · by_cases h6 : k = 6
    · subst h6; simp
    · by_cases h5 : k = 5
      · subst h5; simp
      · by_cases h4 : k = 4
        · subst h4; simp
        · by_cases h3 : k = 3
          · subst h3; simp
          · by_cases h2 : k = 2
            · subst h2; simp
            · by_cases h1 : k = 1
              · subst h1; simp
              · by_cases h0 : k = 0
                · subst h0; simp
                · have hnlt : ¬ (k < 8) := by omega
                  simp [h7, h6, h5, h4, h3, h2, h1, h0, hnlt]

/-- Models `rustc 1.99.1 -O` lowering of `ct_lookup8_naive_rust` (`cmp rsi, 7; ja; jmp [table+rsi*4]`
    + `mov rax, [rdi + 8*rsi]`): functionally equivalent to `lookup8Spec`, yet leaks `secret_idx`
    through both branch and memory-address events! -/
def llvmJumpTableLowering (s : X86State) : Nat × List LeakEvent :=
  let idx := s.gpr .rsi % W64
  let base := s.gpr .rdi
  if idx < 8 then
    (readMem64 s ((base + 8 * idx) % W64),
     s.leak ++ [.branch false 0x3d, .load64 ((base + 8 * idx) % W64)])
  else
    (0, s.leak ++ [.branch true 0x3d])

theorem llvm_jump_table_functional_but_leaks (s1 s2 : X86State)
    (hpub : s1.gpr .rdi = s2.gpr .rdi) (hleak : s1.leak = s2.leak)
    (hbase : s1.gpr .rdi + 56 < W64)
    (hsec1 : s1.gpr .rsi % W64 = 0) (hsec2 : s2.gpr .rsi % W64 = 1) :
    (llvmJumpTableLowering s1).1 = lookup8Spec s1 (s1.gpr .rdi) (s1.gpr .rsi % W64) ∧
    (llvmJumpTableLowering s2).1 = lookup8Spec s2 (s2.gpr .rdi) (s2.gpr .rsi % W64) ∧
    (llvmJumpTableLowering s1).2 ≠ (llvmJumpTableLowering s2).2 := by
  unfold llvmJumpTableLowering lookup8Spec
  rw [hsec1, hsec2, ← hpub, ← hleak]
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  refine ⟨rfl, rfl, ?_⟩
  intro heq
  dsimp at heq
  have h1 : [LeakEvent.branch false 61, LeakEvent.load64 (s1.gpr .rdi % W64)] =
            [LeakEvent.branch false 61, LeakEvent.load64 ((s1.gpr .rdi + 8) % W64)] := by
    revert heq
    induction s1.leak with
    | nil => intro h; exact h
    | cons _ _ ih => intro h; exact ih (List.cons.inj h).2
  injection h1 with _ htl
  injection htl with hhd _
  injection hhd with haddr
  have m0 : s1.gpr .rdi % W64 = s1.gpr .rdi := Nat.mod_eq_of_lt (by omega)
  have m1 : (s1.gpr .rdi + 8) % W64 = s1.gpr .rdi + 8 := Nat.mod_eq_of_lt (by omega)
  rw [m0, m1] at haddr
  omega

end LockedObligations
