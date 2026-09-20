import Lean_Code.PackingReduction

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def crossVec (x y : ℝ³) : ℝ³ :=
  !₂[x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

lemma crossVec_inner_left (x y : ℝ³) : inner ℝ (crossVec x y) x = 0 := by
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  ring

lemma crossVec_inner_right (x y : ℝ³) : inner ℝ (crossVec x y) y = 0 := by
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  ring

lemma crossVec_norm_sq (x y : ℝ³) :
    ‖crossVec x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - inner ℝ x y ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_coordinate_sum]
  simp [crossVec, Fin.sum_univ_succ]
  ring

/-- Two equally long nonzero tangent vectors fit in a closed tangent
semicircle, including the antipodal case. -/
lemma two_tangent_directions (p u v : ℝ³) (hp : ‖p‖ = 1)
    (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0)
    (hu : 0 < ‖u‖) (huv : ‖u‖ = ‖v‖) :
    ∃ w : ℝ³, ‖w‖ = 1 ∧ inner ℝ p w = 0 ∧ inner ℝ w u ≤ 0 ∧ inner ℝ w v ≤ 0 := by
  have hnormalize (w : ℝ³) (hw : 0 < ‖w‖) (hwp : inner ℝ p w = 0)
      (hwu : inner ℝ w u ≤ 0) (hwv : inner ℝ w v ≤ 0) :
      ∃ w : ℝ³, ‖w‖ = 1 ∧ inner ℝ p w = 0 ∧ inner ℝ w u ≤ 0 ∧ inner ℝ w v ≤ 0 := by
    refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw), inv_mul_cancel₀ hw.ne']
    · simp [inner_smul_right, hwp]
    · simpa only [inner_smul_left, starRingEnd_apply, star_trivial] using
        mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hw.le) hwu
    · simpa only [inner_smul_left, starRingEnd_apply, star_trivial] using
        mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hw.le) hwv
  by_cases hs : u + v = 0
  · have hv : v = -u := by
      calc
        v = (u + v) - u := by abel
        _ = -u := by rw [hs, zero_sub]
    have hw : 0 < ‖crossVec p u‖ := by
      have h := crossVec_norm_sq p u
      rw [hp, hpu] at h
      nlinarith [norm_nonneg (crossVec p u), sq_pos_of_pos hu]
    apply hnormalize (crossVec p u) hw
    · rw [real_inner_comm]; exact crossVec_inner_left p u
    · exact (crossVec_inner_right p u).le
    · rw [hv, inner_neg_right, crossVec_inner_right]
      norm_num
  · have hw : 0 < ‖-(u + v)‖ := by rw [norm_neg]; exact norm_pos_iff.mpr hs
    have hinner : -‖u‖ ^ 2 ≤ inner ℝ u v := by
      have h := abs_real_inner_le_norm u v
      rw [← huv] at h
      nlinarith [(abs_le.mp h).1]
    apply hnormalize (-(u + v)) hw
    · simp [inner_neg_right, inner_add_right, hpu, hpv]
    · simp only [inner_neg_left, inner_add_left, real_inner_self_eq_norm_sq]
      rw [real_inner_comm u v]
      linarith
    · simp only [inner_neg_left, inner_add_left, real_inner_self_eq_norm_sq]
      rw [← huv]
      linarith

lemma contact_tangent_norm_sq (p q : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = c) :
    inner ℝ p (q - c • p) = 0 ∧ ‖q - c • p‖ ^ 2 = 1 - c ^ 2 := by
  have hqp : inner ℝ q p = c := (real_inner_comm p q).trans hpq
  constructor
  · simp [inner_sub_right, inner_smul_right, hpq, hp]
  · rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [hpq, hqp]
    simp [real_inner_self_eq_norm_sq, hp, hq]
    ring

lemma two_contacts_semicircle (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    ∃ w : ℝ³, ‖w‖ = 1 ∧ inner ℝ p w = 0 ∧ inner ℝ w q ≤ 0 ∧ inner ℝ w r ≤ 0 := by
  have hq' := contact_tangent_norm_sq p q c hp hq hpq
  have hr' := contact_tangent_norm_sq p r c hp hr hpr
  have hpos : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  have hunorm : 0 < ‖q - c • p‖ := by nlinarith [norm_nonneg (q - c • p)]
  have heqnorm : ‖q - c • p‖ = ‖r - c • p‖ := by
    nlinarith [norm_nonneg (q - c • p), norm_nonneg (r - c • p)]
  obtain ⟨w, hw, hpw, hwq, hwr⟩ := two_tangent_directions p (q - c • p) (r - c • p)
    hp hq'.1 hr'.1 hunorm heqnorm
  have hwp : inner ℝ w p = 0 := (real_inner_comm p w).trans hpw
  simp only [inner_sub_right, inner_smul_right, hwp, mul_zero, sub_zero] at hwq hwr
  exact ⟨w, hw, hpw, hwq, hwr⟩

/-- A nonisolated irreducible vertex has three distinct contact neighbors. -/
theorem irreducible_three_neighbors (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ j, ‖Y j‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin 8)
    (hneighbor : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    ∃ j k l : Fin 8, j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      inner ℝ (Y i) (Y j) = c ∧ inner ℝ (Y i) (Y k) = c ∧ inner ℝ (Y i) (Y l) = c := by
  classical
  obtain ⟨j, hji, hij⟩ := hneighbor
  have hnotpair (k : Fin 8) (hik : inner ℝ (Y i) (Y k) = c) :
      ∃ l, l ≠ i ∧ inner ℝ (Y i) (Y l) = c ∧ l ≠ j ∧ l ≠ k := by
    by_contra h
    push_neg at h
    obtain ⟨w, hw, hiw, hwj, hwk⟩ := two_contacts_semicircle (Y i) (Y j) (Y k) c
      (hY i) (hY j) (hY k) hc hij hik
    apply hirr i ⟨j, hji, hij⟩
    refine ⟨w, hw, hiw, ?_⟩
    intro l hli hil
    by_cases hlj : l = j
    · simpa [hlj] using hwj
    · have hlk := h l hli hil hlj
      simpa [hlk] using hwk
  obtain ⟨k, hki, hik, hkj, hkj'⟩ := hnotpair j hij
  obtain ⟨l, hli, hil, hlj, hlk⟩ := hnotpair k hik
  exact ⟨j, k, l, hji, hki, hli, hkj.symm, hlj.symm, hlk.symm, hij, hik, hil⟩

end SquareAntiprismVerification
