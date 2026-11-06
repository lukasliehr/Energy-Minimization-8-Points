import Blueprint.Tail

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem cos_two_pi_fifths : cos (2*Real.pi/5)=(sqrt 5-1)/4 := by
  have hs : sqrt 5^2=(5:ℝ) := Real.sq_sqrt (by norm_num)
  rw [show 2*Real.pi/5=2*(Real.pi/5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith

theorem constants_angle_cutoff (c : ℝ) (hc : 0<c) (hcupper : c<3/10) :
    2*Real.pi/5<arccos c ∧ arccos c<arccos (c/(1+c)) ∧
    arccos (c/(1+c))<Real.pi/2 := by
  have hs : sqrt 5^2=(5:ℝ) := Real.sq_sqrt (by norm_num)
  have hroot : (11:ℝ)/5<sqrt 5 := by nlinarith [Real.sqrt_nonneg (5:ℝ)]
  have hcos : c<cos (2*Real.pi/5) := by rw [cos_two_pi_fifths]; linarith
  have htheta := Real.arccos_lt_arccos (by linarith : -1≤c) hcos (Real.cos_le_one _)
  rw [Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at htheta
  have hden : 0<1+c := by linarith
  have hratio : 0<c/(1+c) := div_pos hc hden
  have hrlt : c/(1+c)<c := (div_lt_iff₀ hden).mpr (by nlinarith [sq_pos_of_pos hc])
  exact ⟨htheta, Real.arccos_lt_arccos (by linarith) hrlt (by linarith),
    Real.arccos_lt_pi_div_two.mpr hratio⟩

theorem equilateral_angle_gt_two_pi_fifths (c : ℝ) (hc : 0<c) (hcupper : c<3/10) :
    2*Real.pi/5<arccos (c/(1+c)) :=
  lt_trans (constants_angle_cutoff c hc hcupper).1 (constants_angle_cutoff c hc hcupper).2.1

#print axioms constants_angle_cutoff
end Blueprint.Thomson.Tail.Implementation
