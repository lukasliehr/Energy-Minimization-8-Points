import AllS.Units.N_GI.N_pair_hessian.N_chart_bounds
import AllS.Units.N_GI.N_derivative_stability.N_pair_derivative

noncomputable section
open Real Filter
namespace Blueprint.Thomson.Tail.Implementation

def pairSecond (q ξ : TangentCoordinates) (i j : Fin 8) : ℝ :=
  -2*(inner ℝ (chartSecond q ξ i) (orthographicChart q j)+
    2*inner ℝ (chartDerivative q i ξ) (chartDerivative q j ξ)+
    inner ℝ (orthographicChart q i) (chartSecond q ξ j))

theorem chart_line_in_ball (q ξ : TangentCoordinates) (hq : ‖q‖<1) :
    ∀ᶠ t : ℝ in nhds 0, ‖q+t • ξ‖<1 := by
  have hc : ContinuousAt (fun t : ℝ=>‖q+t • ξ‖) 0 := by fun_prop
  have hh : ‖q+(0:ℝ) • ξ‖<1 := by simpa using hq
  exact hc.eventually (isOpen_Iio.mem_nhds hh)

theorem pairDerivative_line_hasDerivAt (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    HasDerivAt (fun t : ℝ=>pairDerivative (q+t • ξ) i j ξ) (pairSecond q ξ i j) 0 := by
  have hi := (pair_hessian_chart_second q ξ hq i).inner ℝ (chart_line_hasDerivAt q ξ hq j)
  have hj := (chart_line_hasDerivAt q ξ hq i).inner ℝ (pair_hessian_chart_second q ξ hq j)
  have h := (hi.add hj).const_mul (-2:ℝ)
  have hh : HasDerivAt (fun t : ℝ=>-2*(inner ℝ (chartDerivative (q+t • ξ) i ξ) (orthographicChart (q+t • ξ) j)+
      inner ℝ (orthographicChart (q+t • ξ) i) (chartDerivative (q+t • ξ) j ξ))) (pairSecond q ξ i j) 0 := by
    convert! h using 1
    simp only [pairSecond,zero_smul,add_zero]
    ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [chart_line_in_ball q ξ hq] with t ht
  exact pairDerivative_apply (q+t • ξ) ξ ht i j

theorem pairSecond_identity (q ξ : TangentCoordinates) (i j : Fin 8) :
    pairSecond q ξ i j =
      2*chartSecondCoefficient q ξ i*inner ℝ (packingReference i) (orthographicChart q j)+
      2*chartSecondCoefficient q ξ j*inner ℝ (packingReference j) (orthographicChart q i)-
      4*inner ℝ (chartDerivative q i ξ) (chartDerivative q j ξ) := by
  simp only [pairSecond,chartSecond,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm (orthographicChart q i) (packingReference j)]
  ring

#print axioms pairDerivative_line_hasDerivAt
end Blueprint.Thomson.Tail.Implementation
