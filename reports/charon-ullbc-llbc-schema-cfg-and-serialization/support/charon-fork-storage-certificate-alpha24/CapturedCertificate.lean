import ForkModel
namespace CharonFork
def sourceIdentity : String := "cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0"
def originalExportIdentity : String := "6eaeff5984f14a4a081b9573f58e9f852bd41e2fb3c7c1e90954f8ff54476196"
def finalExportIdentity : String := "1337e82833904551d1762437233ad1d80edbb4579735790adcecb6ceda1d5764"
-- Consumer-decoded, data-only exact selected instruction/edge descriptors.
def selectedBefore : List Block :=
 [⟨[.live 4, .copy 4 1], .branch 4 1 2⟩,
  ⟨[.copy 0 2], .jump 3⟩, ⟨[.copy 0 3], .jump 3⟩, ⟨[.dead 4], .ret⟩]
def selectedAfter : Fork := ⟨[.live 4, .copy 4 1], 4, [.copy 0 2], [.copy 0 3], [.dead 4]⟩
theorem captured_claim :
 sourceIdentity = "cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0" ∧
 originalExportIdentity = "6eaeff5984f14a4a081b9573f58e9f852bd41e2fb3c7c1e90954f8ff54476196" ∧
 finalExportIdentity = "1337e82833904551d1762437233ad1d80edbb4579735790adcecb6ceda1d5764" ∧
 ∀ (fuel : Nat) (state : State),
   runCFG selectedBefore (fuel + 3) 0 state = runStructured selectedAfter state :=
 ⟨rfl, rfl, rfl, fun fuel state => graph_fork raw fuel state⟩
#print captured_claim
#print axioms captured_claim
end CharonFork
