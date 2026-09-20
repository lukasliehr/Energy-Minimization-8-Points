import Lean_Code.FiniteArcPatchCover

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A small closed spherical cap intersected with closed great-circle
halfspaces. These are the local interior, edge, and strict-corner models. -/
def sphericalHalfspacePatch {ι : Type*} (normal : ι → ℝ³) (p : ℝ³) (δ : ℝ) : Set ℝ³ :=
  {x | ‖x‖ = 1 ∧ δ ≤ inner ℝ p x ∧ ∀ i, 0 ≤ inner ℝ (normal i) x}

theorem sphericalHalfspacePatch_isClosed {ι : Type*} (normal : ι → ℝ³) (p : ℝ³) (δ : ℝ) :
    IsClosed (sphericalHalfspacePatch normal p δ) := by
  have hnorm : IsClosed {x : ℝ³ | ‖x‖ = 1} := isClosed_eq continuous_norm continuous_const
  have hcap : IsClosed {x : ℝ³ | δ ≤ inner ℝ p x} := isClosed_le continuous_const (by fun_prop)
  have hhalf : IsClosed {x : ℝ³ | ∀ i, 0 ≤ inner ℝ (normal i) x} := by
    rw [show {x : ℝ³ | ∀ i, 0 ≤ inner ℝ (normal i) x} =
      ⋂ i, {x : ℝ³ | 0 ≤ inner ℝ (normal i) x} by ext x; simp]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (by fun_prop))
  exact hnorm.inter (hcap.inter hhalf)

theorem sphericalHalfspacePatch_isCompact {ι : Type*} (normal : ι → ℝ³) (p : ℝ³) (δ : ℝ) :
    IsCompact (sphericalHalfspacePatch normal p δ) := by
  apply spherePoint_isCompact.of_isClosed_subset (sphericalHalfspacePatch_isClosed normal p δ)
  intro x hx
  exact hx.1

lemma sphericalHalfspacePatch_nonantipodal {ι : Type*} (normal : ι → ℝ³) (p : ℝ³)
    (δ : ℝ) (hδ : 0 < δ) (a b : ℝ³)
    (ha : a ∈ sphericalHalfspacePatch normal p δ) (hb : b ∈ sphericalHalfspacePatch normal p δ) :
    a ≠ -b := by
  intro heq
  have ha' := ha.2.1
  have hb' := hb.2.1
  rw [heq, inner_neg_right] at ha'
  linarith

lemma unit_affine_combination_norm_le_one (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(1 - t) • a + t • b‖ ≤ 1 := by
  have h := norm_add_le ((1 - t) • a) (t • b)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1, ha, hb] at h
  linarith

theorem sphericalHalfspacePatch_arcClosed {ι : Type*} (normal : ι → ℝ³) (p : ℝ³)
    (δ : ℝ) (hδ : 0 < δ) : ShortArcClosed (sphericalHalfspacePatch normal p δ) := by
  intro a ha b hb hanti t ht
  have hnpos : 0 < ‖(1 - t) • a + t • b‖ := norm_pos_iff.mpr
    (shortSphereArc_combination_ne_zero a b ha.1 hb.1 hanti t ht)
  have hnle := unit_affine_combination_norm_le_one a b ha.1 hb.1 t ht
  refine ⟨shortSphereArc_unit a b ha.1 hb.1 hanti t ht, ?_, ?_⟩
  · have hlin : δ ≤ inner ℝ p ((1 - t) • a + t • b) := by
      simp only [inner_add_right, inner_smul_right]
      nlinarith [mul_le_mul_of_nonneg_left ha.2.1 (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left hb.2.1 ht.1]
    change δ ≤ inner ℝ p (sphereNormalize ((1 - t) • a + t • b))
    rw [sphereNormalize_inner, mul_comm, ← div_eq_mul_inv]
    apply (le_div_iff₀ hnpos).mpr
    exact (mul_le_mul_of_nonneg_left hnle hδ.le).trans (by simpa using hlin)
  · intro i
    change 0 ≤ inner ℝ (normal i) (sphereNormalize ((1 - t) • a + t • b))
    rw [sphereNormalize_inner]
    apply mul_nonneg (inv_nonneg.mpr hnpos.le)
    simp only [inner_add_right, inner_smul_right]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (ha.2.2 i))
      (mul_nonneg ht.1 (hb.2.2 i))

end SquareAntiprismVerification
