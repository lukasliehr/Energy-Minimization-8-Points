import Lean_Code.LocalChart

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def lineReflection (u : ℝ³) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ := (ℝ ∙ u).reflection

lemma lineReflection_apply (u x : ℝ³) :
    lineReflection u x = (2 * inner ℝ u x / ‖u‖ ^ 2) • u - x := by
  rw [lineReflection, Submodule.reflection_singleton_apply, two_smul]
  rw [show 2 * inner ℝ u x / ‖u‖ ^ 2 =
    inner ℝ u x / ‖u‖ ^ 2 + inner ℝ u x / ‖u‖ ^ 2 by ring, add_smul]
  norm_cast

lemma lineReflection_self (u : ℝ³) : lineReflection u u = u := by
  exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self u)

lemma lineReflection_involutive (u x : ℝ³) :
    lineReflection u (lineReflection u x) = x :=
  Submodule.reflection_reflection _ _

lemma lineReflection_orthogonal (u x : ℝ³) (h : inner ℝ u x = 0) :
    lineReflection u x = -x := by simp [lineReflection_apply, h]

lemma lineReflection_sum (a b : ℝ³) (h : ‖a‖ = ‖b‖) :
    lineReflection (a + b) a = b := by
  by_cases hab : a + b = 0
  · have hb : b = -a := eq_neg_of_add_eq_zero_right hab
    simp [lineReflection_apply, hab, hb]
  have hn : ‖a + b‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hab))
  have hinner : 2 * inner ℝ (a + b) a = ‖a + b‖ ^ 2 := by
    rw [inner_add_left, real_inner_self_eq_norm_sq, norm_add_sq_real, real_inner_comm b a, h]
    ring
  have hcoef : 2 * inner ℝ (a + b) a / ‖a + b‖ ^ 2 = 1 := by rw [hinner]; exact div_self hn
  rw [lineReflection_apply, hcoef, one_smul]
  abel

/-- A continuous near-identity orthogonal alignment of equal-length vectors.
The two line reflections cancel when the vectors agree. -/
def alignVector (a b : ℝ³) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  (lineReflection (a + b)).trans (lineReflection b)

lemma alignVector_apply (a b x : ℝ³) :
    alignVector a b x = lineReflection b (lineReflection (a + b) x) := rfl

lemma alignVector_maps (a b : ℝ³) (h : ‖a‖ = ‖b‖) : alignVector a b a = b := by
  rw [alignVector_apply, lineReflection_sum a b h, lineReflection_self]

lemma lineReflection_two (u x : ℝ³) : lineReflection (u + u) x = lineReflection u x := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hu))
  rw [lineReflection_apply, lineReflection_apply,
    show u + u = (2 : ℝ) • u by module, norm_smul, inner_smul_left, smul_smul]
  congr 2
  norm_num
  field_simp

lemma alignVector_self (u x : ℝ³) : alignVector u u x = x := by
  rw [alignVector_apply, lineReflection_two, lineReflection_involutive]

lemma alignVector_preserves_orthogonal (a b x : ℝ³)
    (ha : inner ℝ a x = 0) (hb : inner ℝ b x = 0) : alignVector a b x = x := by
  rw [alignVector_apply, lineReflection_orthogonal (a + b) x (by simp [inner_add_left, ha, hb]),
    map_neg, lineReflection_orthogonal b x hb, neg_neg]

lemma lineReflection_continuousAt (u x : ℝ³) (hu : u ≠ 0) :
    ContinuousAt (fun p : ℝ³ × ℝ³ => lineReflection p.1 p.2) (u, x) := by
  simp only [lineReflection_apply]
  fun_prop (disch := exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hu)))

lemma alignVector_continuousAt (a b x : ℝ³) (hab : a + b ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun p : (ℝ³ × ℝ³) × ℝ³ => alignVector p.1.1 p.1.2 p.2) ((a, b), x) := by
  simp only [alignVector_apply, lineReflection_apply]
  fun_prop (disch := first
    | exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hb))
    | exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hab)))

end SquareAntiprismVerification
