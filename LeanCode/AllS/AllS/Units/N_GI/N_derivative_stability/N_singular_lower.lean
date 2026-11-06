import AllS.Units.N_GI.N_derivative_stability.N_operator_error
import AllS.Units.N_GI.N_convex_domain.N_sublevel_bridge

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem referenceContactMap_norm_lower (ξ : TangentCoordinates) (hξ : ξ∈rotationSlice) :
    √3*‖ξ‖≤‖referenceContactMap ξ‖ := by
  have h := contact_spectrum_physical_unweighted ξ hξ
  have he : ‖referenceContactMap ξ‖^2=∑ e : ContactIndex, (contactLinear ξ e.1 (contactNext e))^2 := by
    simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hp : 0≤√3*‖ξ‖ := by positivity
  nlinarith [norm_nonneg (referenceContactMap ξ)]

theorem contactDerivativeMap_norm_lower (q ξ : TangentCoordinates) (hq : ‖q‖≤3/10)
    (hξ : ξ∈rotationSlice) :
    (√3-12*‖q‖)*‖ξ‖≤‖contactDerivativeMap q ξ‖ := by
  have hR := referenceContactMap_norm_lower ξ hξ
  have hE := ((contactDerivativeMap q-referenceContactMap).le_opNorm ξ).trans
    (mul_le_mul_of_nonneg_right (derivative_stability_operator_error q hq) (norm_nonneg ξ))
  have ht : ‖referenceContactMap ξ‖≤‖contactDerivativeMap q ξ‖+
      ‖(contactDerivativeMap q-referenceContactMap) ξ‖ := by
    calc
      _ = ‖contactDerivativeMap q ξ-(contactDerivativeMap q-referenceContactMap) ξ‖ := by simp
      _ ≤ _ := norm_sub_le _ _
  nlinarith

theorem derivative_margin_scalar (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) :
    77/50<√3-12*‖q‖ := by
  have hp0 : 0<p := by linarith
  have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤77/100) (by norm_num : (0:ℝ)<97/2) hp
  change ‖q‖≤(77/100)/p at hq
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hsl : (433:ℝ)/250<√3 := by nlinarith
  norm_num at hh
  linarith

theorem derivative_stability_singular_lower (p : ℝ) (hp : (97:ℝ)/2≤p)
    (q ξ : TangentCoordinates) (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) (hξ0 : ξ≠0) :
    (47:ℝ)/20*‖ξ‖^2<∑ e : ContactIndex, (pairDerivative q e.1 (contactNext e) ξ)^2 := by
  have h := contactDerivativeMap_norm_lower q ξ (tail_small_radius p hp q hq.2.1) hξ
  have hs := mul_lt_mul_of_pos_right (derivative_margin_scalar p hp q hq.2.1) (norm_pos_iff.mpr hξ0)
  have hn := hs.trans_le h
  have he : ‖contactDerivativeMap q ξ‖^2=∑ e : ContactIndex, (pairDerivative q e.1 (contactNext e) ξ)^2 := by
    simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  have hpos := norm_pos_iff.mpr hξ0
  nlinarith [norm_nonneg (contactDerivativeMap q ξ)]

#print axioms derivative_stability_singular_lower
end Blueprint.Thomson.Tail.Implementation
