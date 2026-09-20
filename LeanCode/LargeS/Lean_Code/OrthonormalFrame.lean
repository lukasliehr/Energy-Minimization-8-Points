import Lean_Code.RhombusGram

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def frameLinearMap (e : Fin 3 → ℝ³) : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun x := ∑ i, x i • e i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

lemma frameLinearMap_inner (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (x y : ℝ³) :
    inner ℝ (frameLinearMap e x) (frameLinearMap e y) = inner ℝ x y := by
  change inner ℝ (∑ i, x i • e i) (∑ j, y j • e j) = _
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, he]
  simp [inner_coordinate_sum, mul_comm]

def frameLinearIsometry (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : ℝ³ →ₗᵢ[ℝ] ℝ³ where
  toLinearMap := frameLinearMap e
  norm_map' x := by
    have h := frameLinearMap_inner e he x x
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (frameLinearMap e x), norm_nonneg x]

def frameEquiv (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  LinearIsometryEquiv.ofSurjective (frameLinearIsometry e he)
    (LinearMap.surjective_of_injective (f := (frameLinearIsometry e he).toLinearMap)
      (frameLinearIsometry e he).injective)

lemma frameEquiv_apply (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (x : ℝ³) :
    frameEquiv e he x = ∑ i, x i • e i := rfl

end SquareAntiprismVerification
