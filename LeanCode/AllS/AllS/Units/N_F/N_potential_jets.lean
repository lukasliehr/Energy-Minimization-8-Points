import AllS.Units.N_F.N_definitions
import AllS.Units.N_FI.N_potential_jets.N_tower
import Blueprint.FiniteDefinitions
import Blueprint.FiniteJetPilot
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def NormalizedPotentialJetsContract : Prop :=
  (∀ s t : ℝ, potentialJet s 0 t = phi s t) ∧
  (∀ (s t : ℝ) (m : ℕ), 0 ≤ s → t < 1 →
    HasDerivAt (potentialJet s m) (potentialJet s (m+1) t) t ∧
    ContinuousAt (potentialJet s m) t ∧ (0 < m → 0 < potentialJet s m t)) ∧
  (∀ (s t : ℝ) (m : ℕ), t < 1 →
    potentialJet s (m+1) t =
      2^m * (∏ j ∈ Finset.range m, (s/2+(j : ℝ)+1)) *
        (2-2*t)^(-((m : ℝ)+1)) * (1+s*phi s t)) ∧
  (∀ (s t : ℝ) (m : ℕ), t < 1 →
    potentialJet s (m+2) t =
      (2*(s/2+(m : ℝ)+1)/(2-2*t)) * potentialJet s (m+1) t)

theorem normalized_potential_jets : NormalizedPotentialJetsContract := by
  exact ⟨potentialJet_zero, potential_jets_tower, potentialJet_closed, potentialJet_recurrence⟩

#check normalized_potential_jets
#print axioms normalized_potential_jets
end Blueprint.Thomson.Finite
