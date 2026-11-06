import AllS.Units.N_GI.N_derivative_stability.N_chart_derivative
import AllS.Units.N_GI.N_stationary_chart.N_chart_curve

noncomputable section
open Real Filter
namespace Blueprint.Thomson.Tail.Implementation

def chartSecondCoefficient (q ξ : TangentCoordinates) (i : Fin 8) : ℝ :=
  ‖tangentVector ξ i‖^2/chartRoot q i+
    (inner ℝ (tangentVector q i) (tangentVector ξ i))^2/(chartRoot q i)^3
def chartSecond (q ξ : TangentCoordinates) (i : Fin 8) : Point :=
  -chartSecondCoefficient q ξ i • packingReference i

theorem chart_line_hasDerivAt (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    HasDerivAt (fun t : ℝ=>orthographicChart (q+t • ξ) i) (chartDerivative q i ξ) 0 := by
  have hline : HasDerivAt (fun t : ℝ=>q+t • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const ξ).const_add q
  have hc : HasFDerivAt (fun z=>orthographicChart z i) (chartDerivative q i) (q+(0:ℝ) • ξ) := by
    simpa using derivative_stability_chart_derivative q hq i
  exact hc.comp_hasDerivAt 0 hline

theorem chartRoot_line_hasDerivAt (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    HasDerivAt (fun t : ℝ=>chartRoot (q+t • ξ) i)
      (-inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i) 0 := by
  have ht : HasDerivAt (fun t : ℝ=>tangentVector (q+t • ξ) i) (tangentVector ξ i) 0 := by
    simpa only [chart_line_tangent,zero_smul,add_zero,id_eq,one_smul] using
      ((hasDerivAt_id (0:ℝ)).smul_const (tangentVector ξ i)).const_add (tangentVector q i)
  have hb : 0<1-‖tangentVector q i‖^2 := by
    have hn := (tangentVector_norm_le q i).trans_lt hq
    nlinarith [norm_nonneg (tangentVector q i)]
  have h := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub ht.norm_sq).sqrt (by simpa using hb.ne')
  have hh : HasDerivAt (fun t : ℝ=>chartRoot (q+t • ξ) i)
      ((-2*inner ℝ (tangentVector q i) (tangentVector ξ i))/(2*chartRoot q i)) 0 := by
    simpa [chartRoot] using h
  convert hh using 1 <;> ring

theorem pair_hessian_chart_second (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    HasDerivAt (fun t : ℝ=>chartDerivative (q+t • ξ) i ξ) (chartSecond q ξ i) 0 := by
  have hs := lt_of_lt_of_le (chartRoot_bounds q hq i).1 (chartRoot_bounds q hq i).2.1
  have ht : HasDerivAt (fun t : ℝ=>tangentVector (q+t • ξ) i) (tangentVector ξ i) 0 := by
    simpa only [chart_line_tangent,zero_smul,add_zero,id_eq,one_smul] using
      ((hasDerivAt_id (0:ℝ)).smul_const (tangentVector ξ i)).const_add (tangentVector q i)
  have hn := ht.inner ℝ (hasDerivAt_const (0:ℝ) (tangentVector ξ i))
  have hquot := hn.div (chartRoot_line_hasDerivAt q ξ hq i) (by simpa using hs.ne')
  have h := (hasDerivAt_const (0:ℝ) (tangentVector ξ i)).sub (hquot.smul_const (packingReference i))
  have he : (fun t : ℝ=>chartDerivative (q+t • ξ) i ξ)=
      fun t : ℝ=>tangentVector ξ i-(inner ℝ (tangentVector (q+t • ξ) i) (tangentVector ξ i)/chartRoot (q+t • ξ) i) • packingReference i := by
    funext t;exact chartDerivative_apply _ _ _
  rw [he]
  convert! h using 1
  simp only [chartSecond,chartSecondCoefficient,zero_smul,add_zero,inner_zero_right,add_zero,
    real_inner_self_eq_norm_sq,zero_sub,←neg_smul]
  congr 1
  field_simp [hs.ne']
  <;> ring

#print axioms pair_hessian_chart_second
end Blueprint.Thomson.Tail.Implementation
