import AllS.Units.N_GI.N_balanced_energy.N_distinct_chart
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def tangentCLM (i : Fin 8) : TangentCoordinates →L[ℝ] Point :=
  (show TangentCoordinates →ₗ[ℝ] Point from
    { toFun := fun q=>tangentVector q i
      map_add' := fun q v=>tangentVector_add q v i
      map_smul' := fun c q=>tangentVector_smul c q i }).toContinuousLinearMap

@[simp] theorem tangentCLM_apply (i : Fin 8) (q : TangentCoordinates) :
    tangentCLM i q=tangentVector q i := rfl

def chartDerivative (q : TangentCoordinates) (i : Fin 8) : TangentCoordinates →L[ℝ] Point :=
  tangentCLM i - (1/chartRoot q i) •
    (((innerSL ℝ (tangentVector q i)).comp (tangentCLM i)).smulRight (packingReference i))

@[simp] theorem chartDerivative_apply (q ξ : TangentCoordinates) (i : Fin 8) :
    chartDerivative q i ξ=tangentVector ξ i-
      (inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i) • packingReference i := by
  simp only [chartDerivative,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,tangentCLM_apply]
  module

theorem derivative_stability_chart_derivative (q : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    HasFDerivAt (fun z=>orthographicChart z i) (chartDerivative q i) q := by
  have ht := (tangentCLM i).hasFDerivAt (x := q)
  have hbase : 0<1-‖tangentVector q i‖^2 := by
    have hn := (tangentVector_norm_le q i).trans_lt hq
    nlinarith [norm_nonneg (tangentVector q i)]
  have h := (((hasFDerivAt_const (1:ℝ) q).sub ht.norm_sq).sqrt hbase.ne').smul_const (packingReference i)
  have hh := h.add ht
  have hhh : HasFDerivAt (fun z=>orthographicChart z i)
      (((1/(2*chartRoot q i)) • (0-2 • (innerSL ℝ (tangentVector q i)).comp (tangentCLM i))).smulRight (packingReference i)+tangentCLM i) q := hh
  convert hhh using 1
  ext ξ : 1
  simp only [chartDerivative_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,innerSL_apply_apply,tangentCLM_apply,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,zero_sub]
  change tangentVector ξ i - (inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i) • packingReference i =
    ((1/(2*chartRoot q i))*(-(2*inner ℝ (tangentVector q i) (tangentVector ξ i)))) • packingReference i+tangentVector ξ i
  module

#print axioms derivative_stability_chart_derivative
end Blueprint.Thomson.Tail.Implementation
