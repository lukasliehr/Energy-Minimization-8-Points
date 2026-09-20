import Lean_Code.ContactGeometryGlobal

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sphereNormalize (x : ℝ³) : ℝ³ := ‖x‖⁻¹ • x
def hemisphereChart (p x : ℝ³) : ℝ³ := (inner ℝ p x)⁻¹ • x

lemma inner_pos_ne_zero (p x : ℝ³) (h : 0 < inner ℝ p x) : x ≠ 0 := by
  intro hx
  rw [hx, inner_zero_right] at h
  exact lt_irrefl _ h

lemma sphereNormalize_unit (x : ℝ³) (hx : x ≠ 0) : ‖sphereNormalize x‖ = 1 := by
  simp [sphereNormalize, norm_smul, norm_ne_zero_iff.mpr hx]

lemma sphereNormalize_inner (p x : ℝ³) :
    inner ℝ p (sphereNormalize x) = ‖x‖⁻¹ * inner ℝ p x := by
  simp [sphereNormalize, inner_smul_right]

lemma sphereNormalize_inner_pos (p x : ℝ³) (h : 0 < inner ℝ p x) :
    0 < inner ℝ p (sphereNormalize x) := by
  rw [sphereNormalize_inner]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (inner_pos_ne_zero p x h))) h

lemma hemisphereChart_inner (p x : ℝ³) (h : inner ℝ p x ≠ 0) :
    inner ℝ p (hemisphereChart p x) = 1 := by
  simp [hemisphereChart, inner_smul_right, h]

lemma hemisphereChart_normalize (p x : ℝ³) (h : 0 < inner ℝ p x) :
    hemisphereChart p (sphereNormalize x) = hemisphereChart p x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (inner_pos_ne_zero p x h)
  unfold hemisphereChart sphereNormalize
  simp only [inner_smul_right, smul_smul]
  congr 1
  field_simp [hn, h.ne']

lemma normalize_hemisphereChart (p x : ℝ³) (hx : ‖x‖ = 1) (h : 0 < inner ℝ p x) :
    sphereNormalize (hemisphereChart p x) = x := by
  unfold hemisphereChart sphereNormalize
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), hx, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ h.ne', one_smul]

lemma hemisphereChart_inverse (p x : ℝ³) (h : inner ℝ p x = 1) :
    hemisphereChart p (sphereNormalize x) = x := by
  rw [hemisphereChart_normalize p x (by rw [h]; norm_num)]
  simp [hemisphereChart, h]

lemma hemisphereChart_continuousAt (p x : ℝ³) (h : inner ℝ p x ≠ 0) :
    ContinuousAt (hemisphereChart p) x := by
  unfold hemisphereChart
  fun_prop

lemma sphereNormalize_continuousAt (x : ℝ³) (hx : x ≠ 0) : ContinuousAt sphereNormalize x := by
  unfold sphereNormalize
  fun_prop (disch := exact norm_ne_zero_iff.mpr hx)

lemma positive_segment_inner (p a b : ℝ³) (t : ℝ)
    (ha : 0 < inner ℝ p a) (hb : 0 < inner ℝ p b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < inner ℝ p ((1 - t) • a + t • b) := by
  simp only [inner_add_right, inner_smul_right]
  by_cases ht0 : t = 0
  · simpa [ht0] using ha
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) ha.le) (mul_pos htpos hb)

/-- A shorter geodesic segment in one open hemisphere becomes an ordinary
line segment under central projection, with an explicit positive change of
parameter. -/
theorem hemisphereChart_segment (p a b : ℝ³) (t : ℝ)
    (ha : 0 < inner ℝ p a) (hb : 0 < inner ℝ p b) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧
      hemisphereChart p (sphereNormalize ((1 - t) • a + t • b)) =
        (1 - u) • hemisphereChart p a + u • hemisphereChart p b := by
  let d := (1 - t) * inner ℝ p a + t * inner ℝ p b
  have hd : 0 < d := add_pos (mul_pos (by linarith [ht.2]) ha) (mul_pos ht.1 hb)
  let u := t * inner ℝ p b / d
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (mul_pos ht.1 hb) hd, (div_lt_one hd).mpr ?_⟩
    dsimp [d]
    linarith [mul_pos (by linarith [ht.2] : 0 < 1 - t) ha]
  refine ⟨u, hu, ?_⟩
  rw [hemisphereChart_normalize p _ (positive_segment_inner p a b t ha hb ⟨ht.1.le, ht.2.le⟩)]
  unfold hemisphereChart
  simp only [inner_add_right, inner_smul_right, smul_add, smul_smul]
  have hca : d⁻¹ * (1 - t) = (1 - u) * (inner ℝ p a)⁻¹ := by
    dsimp [u]
    field_simp [ha.ne', hd.ne']
    dsimp [d]
    ring
  have hcb : d⁻¹ * t = u * (inner ℝ p b)⁻¹ := by
    dsimp [u]
    field_simp [hb.ne', hd.ne']
  change (d⁻¹ * (1 - t)) • a + (d⁻¹ * t) • b = _
  rw [hca, hcb]

theorem normalized_positive_combination_hemisphere {ι : Type*} [Fintype ι]
    (p : ℝ³) (V : ι → ℝ³) (w : ι → ℝ)
    (hV : ∀ i, 0 < inner ℝ p (V i)) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    0 < inner ℝ p (sphereNormalize (∑ i, w i • V i)) := by
  apply sphereNormalize_inner_pos
  simp only [inner_sum, inner_smul_right]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hw i) (hV i).le
  · obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_univ _, mul_pos hi (hV i)⟩

abbrev openUnitHemisphere (p : ℝ³) := {x : ℝ³ // ‖x‖ = 1 ∧ 0 < inner ℝ p x}
abbrev hemisphereAffinePlane (p : ℝ³) := {x : ℝ³ // inner ℝ p x = 1}

def hemisphereHomeomorph (p : ℝ³) : openUnitHemisphere p ≃ₜ hemisphereAffinePlane p where
  toFun x := ⟨hemisphereChart p x.val, hemisphereChart_inner p x.val x.property.2.ne'⟩
  invFun x := ⟨sphereNormalize x.val,
    sphereNormalize_unit x.val (inner_pos_ne_zero p x.val (by rw [x.property]; norm_num)),
    sphereNormalize_inner_pos p x.val (by rw [x.property]; norm_num)⟩
  left_inv x := Subtype.ext (normalize_hemisphereChart p x.val x.property.1 x.property.2)
  right_inv x := Subtype.ext (hemisphereChart_inverse p x.val x.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hinner : Continuous (fun x : openUnitHemisphere p => inner ℝ p x.val) := by fun_prop
    exact (hinner.inv₀ (fun x => x.property.2.ne')).smul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hnorm : Continuous (fun x : hemisphereAffinePlane p => ‖x.val‖) := by fun_prop
    have hn : ∀ x : hemisphereAffinePlane p, ‖x.val‖ ≠ 0 := by
      intro x
      exact norm_ne_zero_iff.mpr (inner_pos_ne_zero p x.val (by rw [x.property]; norm_num))
    exact (hnorm.inv₀ hn).smul continuous_subtype_val

theorem hemisphereChart_halfspace (p n x : ℝ³) (hx : 0 < inner ℝ p x) :
    (0 < inner ℝ n (hemisphereChart p x) ↔ 0 < inner ℝ n x) ∧
      (0 ≤ inner ℝ n (hemisphereChart p x) ↔ 0 ≤ inner ℝ n x) ∧
      (inner ℝ n (hemisphereChart p x) = 0 ↔ inner ℝ n x = 0) := by
  have hpos : 0 < (inner ℝ p x)⁻¹ := inv_pos.mpr hx
  simp only [hemisphereChart, inner_smul_right]
  exact ⟨mul_pos_iff_of_pos_left hpos, mul_nonneg_iff_of_pos_left hpos, mul_eq_zero_iff_left hpos.ne'⟩

end SquareAntiprismVerification
