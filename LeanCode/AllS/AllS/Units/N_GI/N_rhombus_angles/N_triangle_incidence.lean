import AllS.Units.N_GI.N_rhombus_angles.N_alternating

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_angles_angle_weight_bound (t q : ℕ) (α : ℝ) (θ : Fin q → ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi/2))
    (hθ : ∀ j, θ j < 2*α) (hsum : (t:ℝ)*α + ∑ j, θ j = 2*Real.pi) :
    5 ≤ t+2*q := by
  have hle : (∑ j, θ j) ≤ (q:ℝ)*(2*α) := by
    calc
      _ ≤ ∑ _j : Fin q, 2*α := Finset.sum_le_sum (fun j _ => (hθ j).le)
      _ = _ := by simp
  by_contra hn
  have hnat : t+2*q ≤ 4 := by omega
  have hr : (t:ℝ)+2*(q:ℝ) ≤ 4 := by exact_mod_cast hnat
  have hp := mul_le_mul_of_nonneg_right hr hα.1.le
  nlinarith [hα.2]

theorem rhombus_angles_triangle_incidence (t q d : ℕ) (α : ℝ) (θ : Fin q → ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi/2))
    (hθ : ∀ j, θ j < 2*α) (hsum : (t:ℝ)*α + ∑ j, θ j = 2*Real.pi)
    (hdegree : t+q=d) :
    (d=3 → t≤1) ∧ (d=4 → t≤3) := by
  have h := rhombus_angles_angle_weight_bound t q α θ hα hθ hsum
  omega

#print axioms rhombus_angles_triangle_incidence

end Blueprint.Thomson.Tail.Implementation
