import AllS.Units.N_FI.N_geometry.N_distance_domain

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def EnergyNormalizationContract : Prop := ∀ s : ℝ, 0 ≤ s →
  ∀ Y : Configuration, IsConfiguration Y →
    (s = 0 → E s Y = Ehat s Y) ∧ (0 < s → E s Y = s*Ehat s Y+28)
theorem pair_energy_log (x y : Point) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -Real.log ‖x-y‖ = phi 0 (inner ℝ x y) := by
  have h := norm_sub_sq_real x y
  rw [hx,hy] at h
  have he : 2-2*inner ℝ x y = ‖x-y‖^2 := by nlinarith
  rw [phi_zero, he, Real.log_pow]
  ring

theorem pair_energy_riesz (s : ℝ) (hs : s ≠ 0) (x y : Point)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x-y‖^(-s) = s*phi s (inner ℝ x y)+1 := by
  have h := norm_sub_sq_real x y
  rw [hx,hy] at h
  have he : 2-2*inner ℝ x y = ‖x-y‖^2 := by nlinarith
  have hp : (‖x-y‖^2)^(-s/2) = ‖x-y‖^(-s) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg (x-y)) 2]
    congr 1
    ring
  rw [phi_of_ne_zero s _ hs, he, hp]
  field_simp
  <;> ring

theorem PairSum_one : PairSum (fun _ _ => 1) = 28 := by
  have h : (∑ i : Fin 8, ∑ j : Fin 8 with i < j, (1 : ℕ)) = 28 := by decide
  change (∑ i : Fin 8, ∑ j : Fin 8 with i < j, (1 : ℝ)) = 28
  simpa only [Nat.cast_sum, Nat.cast_one, Nat.cast_ofNat] using
    congrArg (fun n : ℕ => (n : ℝ)) h

theorem PairSum_add (f g : Fin 8 → Fin 8 → ℝ) :
    PairSum (fun i j => f i j+g i j) = PairSum f+PairSum g := by
  simp [PairSum, Finset.sum_add_distrib]

theorem PairSum_mul (s : ℝ) (f : Fin 8 → Fin 8 → ℝ) :
    PairSum (fun i j => s*f i j) = s*PairSum f := by
  simp [PairSum, Finset.mul_sum]

theorem geometry_energy_normalization : EnergyNormalizationContract := by
  intro s hs Y hY
  constructor
  · intro hs0
    subst s
    simp only [E, Ehat, PairSum, if_pos rfl]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact pair_energy_log (Y i) (Y j) (hY.1 i) (hY.1 j)
  · intro hs0
    have hsne : s ≠ 0 := ne_of_gt hs0
    have he : E s Y = PairSum (fun i j => s*phi s (inner ℝ (Y i) (Y j))+1) := by
      unfold E PairSum
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [if_neg hsne]
      exact pair_energy_riesz s hsne (Y i) (Y j) (hY.1 i) (hY.1 j)
    rw [he, PairSum_add, PairSum_mul, PairSum_one]
    rfl

#check geometry_energy_normalization
#print axioms geometry_energy_normalization
#check EnergyNormalizationContract
#print axioms EnergyNormalizationContract
end Blueprint.Thomson.Finite
