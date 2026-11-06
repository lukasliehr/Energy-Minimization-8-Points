import Blueprint.RootBridge
import Blueprint.Tail

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem squaredEnergy_eq_upstream (p : ℝ) (Y : Fin 8 → Point) :
    squaredEnergy p Y = SquareAntiprismVerification.E (2*p) Y := by
  unfold squaredEnergy SquareAntiprismVerification.E
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [squaredDistance, ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg (Y i-Y j))]
  congr 1
  ring

theorem upstream_bridge_energy (s : ℝ) (hs : 0<s) (Y : Fin 8 → Point) :
    E s Y = squaredEnergy (s/2) Y ∧ E s Y = SquareAntiprismVerification.E s Y := by
  have h := squaredEnergy_eq_upstream (s/2) Y
  have he : 2*(s/2)=s := by ring
  rw [he] at h
  exact ⟨(Blueprint.positive_energy_bridge s hs Y).trans h.symm,
    Blueprint.positive_energy_bridge s hs Y⟩

#print axioms squaredEnergy_eq_upstream
#print axioms upstream_bridge_energy
end Blueprint.Thomson.Tail.Implementation
