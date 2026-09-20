import Lean_Code.LocalSphericalModels

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma sphereAngle_pos_of_ne (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hne : a ≠ b) :
    0 < sphereAngle a b := by
  have hr := sphereAngle_range a b
  by_contra hnot
  have hz : sphereAngle a b = 0 := by linarith [hr.1]
  have hi : inner ℝ a b = 1 := by simpa [hz] using (cos_sphereAngle a b ha hb).symm
  have hs : ‖a - b‖ ^ 2 = 0 := by norm_num [norm_sub_sq_real, ha, hb, hi]
  have hn : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp hn))

lemma sphereAngle_lt_pi_of_nonantipodal (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) : sphereAngle a b < Real.pi := by
  have hr := sphereAngle_range a b
  by_contra hnot
  have hz : sphereAngle a b = Real.pi := by linarith [hr.2]
  have hi : inner ℝ a b = -1 := by simpa [hz] using (cos_sphereAngle a b ha hb).symm
  have hs : ‖a + b‖ ^ 2 = 0 := by
    norm_num [norm_add_sq_real, ha, hb, hi]
  have hn : ‖a + b‖ = 0 := by nlinarith [norm_nonneg (a + b)]
  exact hanti (eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hn))

/-- An explicit orthonormal great-circle frame for two distinct,
nonantipodal unit endpoints. -/
theorem short_arc_frame_exists (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hne : a ≠ b) (hanti : a ≠ -b) :
    ∃ t : ℝ³, ‖t‖ = 1 ∧ inner ℝ a t = 0 ∧
      greatCirclePoint a t (sphereAngle a b) = b := by
  let θ := sphereAngle a b
  have hθ0 : 0 < θ := sphereAngle_pos_of_ne a b ha hb hne
  have hθpi : θ < Real.pi := sphereAngle_lt_pi_of_nonantipodal a b ha hb hanti
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  let t := (Real.sin θ)⁻¹ • (b - inner ℝ b a • a)
  have hnorm : ‖b - inner ℝ b a • a‖ = Real.sin θ := by
    simpa only [sphereAngle_comm b a] using unit_projection_norm b a hb ha
  have htunit : ‖t‖ = 1 := by
    simp [t, norm_smul, Real.norm_eq_abs, abs_of_pos hsin, hnorm, hsin.ne']
  have horth : inner ℝ a t = 0 := by
    simp [t, inner_smul_right, inner_sub_right, ha, real_inner_comm b a]
  refine ⟨t, htunit, horth, ?_⟩
  unfold greatCirclePoint
  change Real.cos θ • a + Real.sin θ • t = b
  rw [show Real.cos θ = inner ℝ a b from cos_sphereAngle a b ha hb]
  dsimp [t]
  rw [smul_smul, mul_inv_cancel₀ hsin.ne', one_smul, real_inner_comm b a]
  module

lemma greatCirclePoint_angle (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (a b : ℝ) (hab : |a - b| ≤ Real.pi) :
    sphereAngle (greatCirclePoint m t a) (greatCirclePoint m t b) = |a - b| := by
  unfold sphereAngle
  rw [greatCirclePoint_inner m t hm ht horth]
  rw [← Real.cos_abs (a - b), Real.arccos_cos (abs_nonneg _) hab]

lemma sphereNormalize_pos_smul_unit (z : ℝ³) (hz : ‖z‖ = 1) (r : ℝ) (hr : 0 < r) :
    sphereNormalize (r • z) = z := by
  simp [sphereNormalize, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz,
    smul_smul, hr.ne']

lemma ShortArcClosed.positive_combination {K : Set ℝ³} (hK : ShortArcClosed K)
    (a b : ℝ³) (ha : a ∈ K) (hb : b ∈ K) (hanti : a ≠ -b)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hunit : ‖A • a + B • b‖ = 1) : A • a + B • b ∈ K := by
  let u := B / (A + B)
  have hu : u ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hB hAB.le, (div_le_one hAB).mpr (by linarith)⟩
  have hcomb : (1 - u) • a + u • b = (A + B)⁻¹ • (A • a + B • b) := by
    rw [smul_add, smul_smul, smul_smul]
    have h1 : 1 - u = (A + B)⁻¹ * A := by dsimp [u]; field_simp; ring
    have h2 : u = (A + B)⁻¹ * B := by dsimp [u]; ring
    rw [h1, h2]
  have hmem := hK a ha b hb hanti u hu
  unfold shortSphereArc at hmem
  rw [hcomb, sphereNormalize_pos_smul_unit _ hunit _ (inv_pos.mpr hAB)] at hmem
  exact hmem

lemma greatCirclePoint_sine_combination (m t : ℝ³) (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    greatCirclePoint m t u =
      (Real.sin (θ - u) / Real.sin θ) • m +
        (Real.sin u / Real.sin θ) • greatCirclePoint m t θ := by
  unfold greatCirclePoint
  rw [smul_add, smul_smul, smul_smul]
  have h1 : Real.cos u = Real.sin (θ - u) / Real.sin θ +
      (Real.sin u / Real.sin θ) * Real.cos θ := by
    rw [Real.sin_sub]
    field_simp
    ring
  have h2 : (Real.sin u / Real.sin θ) * Real.sin θ = Real.sin u := by
    field_simp
  rw [h2, h1]
  module

/-- Angular parametrization of a shorter arc stays in every short-arc-closed
patch containing its endpoints. This permits length-preserving subdivision. -/
theorem greatCirclePoint_mem_shortArcClosed {K : Set ℝ³} (hK : ShortArcClosed K)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hmK : m ∈ K) (hbK : greatCirclePoint m t θ ∈ K)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) θ) : greatCirclePoint m t u ∈ K := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  let A := Real.sin (θ - u) / Real.sin θ
  let B := Real.sin u / Real.sin θ
  have hA : 0 ≤ A := div_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hu.2], by linarith [hu.1, hθ.2]⟩) hsin.le
  have hB : 0 ≤ B := div_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨hu.1, hu.2.trans hθ.2.le⟩) hsin.le
  have hrep : greatCirclePoint m t u = A • m + B • greatCirclePoint m t θ :=
    greatCirclePoint_sine_combination m t θ u hsin.ne'
  have hunit : ‖A • m + B • greatCirclePoint m t θ‖ = 1 := by
    rw [← hrep]
    exact greatCirclePoint_unit m t hm ht horth u
  have hAB : 0 < A + B := by
    by_contra hnot
    have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    simp [hA0, hB0] at hunit
  have hanti : m ≠ -greatCirclePoint m t θ := by
    intro heq
    have hne := greatCirclePoint_ne_neg_center m t hm horth θ
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact hne (neg_eq_iff_eq_neg.mp heq.symm)
  rw [hrep]
  exact hK.positive_combination m _ hmK hbK hanti A B hA hB hAB hunit

end SquareAntiprismVerification
