import AllS.Units.N_GI.N_derivative_stability.N_pair_derivative
import AllS.Units.N_GI.N_derivative_stability.N_metric_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def pairErrorBlock (q ξ : TangentCoordinates) (i j : Fin 8) : ℝ :=
  inner ℝ (tangentVector ξ i) (orthographicChart q j-packingReference j)-
    (inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i)*inner ℝ (packingReference i) (orthographicChart q j)

theorem pairErrorBlock_bound (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    |pairErrorBlock q ξ i j| ≤
      (chartStretch ‖q‖*‖tangentVector q j‖+‖tangentVector q i‖/chartMinRoot ‖q‖)*‖tangentVector ξ i‖ := by
  obtain ⟨hs,hi,_⟩ := chartRoot_bounds q hq i
  have hsi : 0<chartRoot q i := hs.trans_le hi
  have hA := (abs_real_inner_le_norm (tangentVector ξ i) (orthographicChart q j-packingReference j)).trans
    (mul_le_mul_of_nonneg_left (chart_deviation_stretch q hq j) (norm_nonneg _))
  have hP : |inner ℝ (packingReference i) (orthographicChart q j)|≤1 := by
    simpa [packingReference_norm,nearest_chart_chart_unit q hq] using
      abs_real_inner_le_norm (packingReference i) (orthographicChart q j)
  have hQ : |inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i|≤
      (‖tangentVector q i‖*‖tangentVector ξ i‖)/chartMinRoot ‖q‖ := by
    rw [abs_div,abs_of_pos hsi]
    exact (div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hsi.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs hi)
  have hB := mul_le_mul hQ hP (abs_nonneg _) (by positivity : 0≤‖tangentVector q i‖*‖tangentVector ξ i‖/chartMinRoot ‖q‖)
  rw [mul_one,←abs_mul] at hB
  have h := norm_sub_le (inner ℝ (tangentVector ξ i) (orthographicChart q j-packingReference j))
    ((inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i)*inner ℝ (packingReference i) (orthographicChart q j))
  simp only [Real.norm_eq_abs] at h
  change |pairErrorBlock q ξ i j|≤_ at h
  calc
    _ ≤ _ := h.trans (add_le_add hA hB)
    _ = _ := by ring

theorem pair_error_abs (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    |pairDerivative q i j ξ-contactLinear ξ i j|≤2*(
      (chartStretch ‖q‖*‖tangentVector q j‖+‖tangentVector q i‖/chartMinRoot ‖q‖)*‖tangentVector ξ i‖+
      (chartStretch ‖q‖*‖tangentVector q i‖+‖tangentVector q j‖/chartMinRoot ‖q‖)*‖tangentVector ξ j‖) := by
  have he : pairDerivative q i j ξ-contactLinear ξ i j =
      -2*(pairErrorBlock q ξ i j+pairErrorBlock q ξ j i) := by
    rw [pairDerivative_error_identity q ξ hq]
    dsimp [pairErrorBlock]
    rw [real_inner_comm (orthographicChart q i-packingReference i) (tangentVector ξ j),
      real_inner_comm (orthographicChart q i) (packingReference j)]
    ring
  rw [he,abs_mul]
  norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
    (add_le_add (pairErrorBlock_bound q ξ hq i j) (pairErrorBlock_bound q ξ hq j i))) (by norm_num)

/-- The two Euclidean block Cauchy inequalities, written without matrix infrastructure. -/
theorem two_slot_error_sq (c b u v x y z : ℝ) (hc : 0≤c) (hb : 0≤b)
    (hu : 0≤u) (hv : 0≤v) (hx : 0≤x) (hy : 0≤y)
    (hz : |z|≤2*((c*v+b*u)*x+(c*u+b*v)*y)) :
    z^2≤4*(c+b)^2*(u^2+v^2)*(x^2+y^2) := by
  have hA : 0≤(c*v+b*u)*x+(c*u+b*v)*y := by positivity
  have hsq : z^2≤4*((c*v+b*u)*x+(c*u+b*v)*y)^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg z) hz
    nlinarith [sq_abs z]
  have hcauchy : ((c*v+b*u)*x+(c*u+b*v)*y)^2≤
      ((c*v+b*u)^2+(c*u+b*v)^2)*(x^2+y^2) := by
    nlinarith [sq_nonneg ((c*v+b*u)*y-(c*u+b*v)*x)]
  have hcoeff : (c*v+b*u)^2+(c*u+b*v)^2≤(c+b)^2*(u^2+v^2) := by
    nlinarith [mul_nonneg (mul_nonneg hc hb) (sq_nonneg (u-v))]
  have hm := mul_le_mul_of_nonneg_right hcoeff (add_nonneg (sq_nonneg x) (sq_nonneg y))
  linarith

theorem pair_error_sq (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    (pairDerivative q i j ξ-contactLinear ξ i j)^2≤
      4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2*
        (‖tangentVector q i‖^2+‖tangentVector q j‖^2)*
        (‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2) := by
  have hs := (chartRoot_bounds q hq i).1
  apply two_slot_error_sq _ _ _ _ _ _ _ (chartStretch_nonneg _) (by positivity)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  convert pair_error_abs q ξ hq i j using 1 <;> ring

def referencePairDerivative (i j : Fin 8) : TangentCoordinates →L[ℝ] ℝ :=
  (-2:ℝ) • ((innerSL ℝ (packingReference j)).comp (tangentCLM i)+
    (innerSL ℝ (packingReference i)).comp (tangentCLM j))

@[simp] theorem referencePairDerivative_apply (ξ : TangentCoordinates) (i j : Fin 8) :
    referencePairDerivative i j ξ=contactLinear ξ i j := by
  simp [referencePairDerivative,contactLinear]
  <;> ring

theorem pair_error_norm (q : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) (hij : i≠j) :
    ‖pairDerivative q i j-referencePairDerivative i j‖ ≤
      2*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)*√(‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by
  have hs := (chartRoot_bounds q hq i).1
  have hc := chartStretch_nonneg ‖q‖
  have hcp : 0≤chartStretch ‖q‖+1/chartMinRoot ‖q‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  simp only [ContinuousLinearMap.sub_apply,referencePairDerivative_apply,Real.norm_eq_abs]
  have hsq := pair_error_sq q ξ hq i j
  have hu := mul_le_mul_of_nonneg_left (tangentVector_pair_norm_sq ξ i j hij)
    (show 0≤4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2*
      (‖tangentVector q i‖^2+‖tangentVector q j‖^2) by positivity)
  have hh := hsq.trans hu
  have he := Real.sq_sqrt (show 0≤‖tangentVector q i‖^2+‖tangentVector q j‖^2 by positivity)
  have hp : 0≤2*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)*
      √(‖tangentVector q i‖^2+‖tangentVector q j‖^2)*‖ξ‖ := by positivity
  have heq : (2*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)*
      √(‖tangentVector q i‖^2+‖tangentVector q j‖^2)*‖ξ‖)^2=
      4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2*(‖tangentVector q i‖^2+‖tangentVector q j‖^2)*‖ξ‖^2 := by
    simp only [mul_pow,he];ring
  nlinarith [sq_abs (pairDerivative q i j ξ-contactLinear ξ i j)]

theorem derivative_stability_row_error (q : TangentCoordinates) (hq : ‖q‖≤3/10)
    (i j : Fin 8) (hij : i≠j) :
    ‖pairDerivative q i j-referencePairDerivative i j‖^2 ≤
      4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by
  have h := mul_self_le_mul_self (norm_nonneg _) (pair_error_norm q (by linarith) i j hij)
  have he := Real.sq_sqrt (show 0≤‖tangentVector q i‖^2+‖tangentVector q j‖^2 by positivity)
  nlinarith

#print axioms derivative_stability_row_error
end Blueprint.Thomson.Tail.Implementation
