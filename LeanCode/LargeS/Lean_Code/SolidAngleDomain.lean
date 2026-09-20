import Lean_Code.SolidAngleDerivative

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- At a unit point outside a contact arc, the corresponding complex angle
term avoids its branch cut. The proof explicitly characterizes that cut by
nonnegative contact-edge coordinates. -/
theorem solidAngleComplex_slit_of_off_arc (a b x : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hoff : x ∉ closedShortSphereArc a b) :
    solidAngleComplex (-x) a b ∈ Complex.slitPlane := by
  by_contra hn
  rw [Complex.mem_slitPlane_iff] at hn
  change ¬(0 < solidAngleDenom (-x) a b ∨ solidAngleNumer (-x) a b ≠ 0) at hn
  push_neg at hn
  have hplane : inner ℝ (crossVec a b) x = 0 := by
    simpa only [solidAngleNumer, inner_neg_right, neg_eq_zero] using hn.2
  let A := contactEdgeCoordinateA a b c x
  let B := contactEdgeCoordinateB a b c x
  have hrep : x = A • a + B • b := contact_coplanar_representation a b x c ha hb hc hab hplane
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hsuminner : inner ℝ x a + inner ℝ x b = (1 + c) * (A + B) := by
    rw [hrep]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_self_eq_norm_sq, ha, hb, hab, hba]
    ring
  have hD : 1 + c ≤ inner ℝ x a + inner ℝ x b := by
    have h := hn.1
    simp only [solidAngleDenom, inner_neg_left, hab] at h
    linarith
  have hsum : 1 ≤ A + B := by
    rw [hsuminner] at hD
    nlinarith [hc.1]
  have hnorm : A ^ 2 + B ^ 2 + 2 * c * A * B = 1 := by
    have hh : inner ℝ x x = 1 := by simp [real_inner_self_eq_norm_sq, hx]
    rw [hrep] at hh
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq, ha, hb, hab, hba] at hh
    nlinarith
  have hAB : 0 ≤ A * B := by
    by_contra hnAB
    have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hc.2) (lt_of_not_ge hnAB)
    nlinarith [sq_nonneg (A + B - 1)]
  have hA : 0 ≤ A := by
    by_contra hnA
    have hAneg : A < 0 := lt_of_not_ge hnA
    have hBpos : 0 < B := by linarith
    exact (not_lt_of_ge hAB) (mul_neg_of_neg_of_pos hAneg hBpos)
  have hB : 0 ≤ B := by
    by_contra hnB
    have hBneg : B < 0 := lt_of_not_ge hnB
    have hApos : 0 < A := by linarith
    exact (not_lt_of_ge hAB) (mul_neg_of_pos_of_neg hApos hBneg)
  exact hoff (closedShortSphereArc_mem_of_positive_combination a b x A B hA hB
    (by linarith) hx hrep)

lemma solidAngleDenom_negative_on_open_arc (a b x : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hx : x ∈ OpenContactArc a b) :
    solidAngleDenom (-x) a b < 0 ∧ solidAngleNumer (-x) a b = 0 := by
  obtain ⟨r, hr0, hr1, hrep⟩ := hx
  let v := (1 - r) • a + r • b
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr (shortSphereArc_combination_ne_zero a b ha hb
    (contact_endpoints_nonantipodal a b hb c hc.1 hab) r ⟨hr0.le, hr1.le⟩)
  have hv1 : ‖v‖ < 1 := by
    have hh := norm_convex_contact_combination_sq a b c r ha hb hab
    have hpos := mul_pos (mul_pos hr0 (sub_pos.mpr hr1)) (sub_pos.mpr hc.2)
    change ‖v‖ ^ 2 = _ at hh
    nlinarith [norm_nonneg v]
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hs : inner ℝ x a + inner ℝ x b = (1 + c) / ‖v‖ := by
    rw [hrep]
    simp only [inner_smul_left, inner_add_left, starRingEnd_apply, star_trivial,
      real_inner_self_eq_norm_sq, ha, hb, hab, hba]
    dsimp [v]
    ring
  constructor
  · have hh : 1 + c < (1 + c) / ‖v‖ := (lt_div_iff₀ hv0).mpr (by
      nlinarith [mul_pos (show 0 < 1 + c by linarith [hc.1]) (sub_pos.mpr hv1)])
    simp only [solidAngleDenom, hab, inner_neg_left]
    rw [← hs] at hh
    linarith
  · rw [hrep]
    simp only [solidAngleNumer, inner_neg_right, inner_smul_right, inner_add_right,
      crossVec_inner_left, crossVec_inner_right, mul_zero, add_zero, neg_zero]

end SquareAntiprismVerification
