import AllS.Units.N_GI.N_nearest_chart.N_chart_unit
import AllS.Units.N_FI.N_contact_order.N_packing_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def chartRoot (q : TangentCoordinates) (i : Fin 8) : ℝ := √(1-‖tangentVector q i‖^2)
def contactLinear (q : TangentCoordinates) (i j : Fin 8) : ℝ :=
  -2*(inner ℝ (packingReference j) (tangentVector q i)+inner ℝ (packingReference i) (tangentVector q j))
def contactQuadratic (q : TangentCoordinates) (i j : Fin 8) : ℝ :=
  packingHeight*(‖tangentVector q i‖^2+‖tangentVector q j‖^2)-2*inner ℝ (tangentVector q i) (tangentVector q j)
def contactRemainder (q : TangentCoordinates) (i j : Fin 8) : ℝ :=
  packingHeight*(chartRoot q i-chartRoot q j)^2+
  2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)+
  2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i)
def contactDelta (q : TangentCoordinates) (i j : Fin 8) : ℝ :=
  squaredDistance (orthographicChart q) i j-tau

theorem chartRoot_sq (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    (chartRoot q i)^2=1-‖tangentVector q i‖^2 := by
  apply Real.sq_sqrt
  have h := (tangentVector_norm_le q i).trans_lt hq
  nlinarith [norm_nonneg (tangentVector q i)]

theorem contact_taylor_exact_expansion (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    contactDelta q i j=contactLinear q i j+contactQuadratic q i j+contactRemainder q i j := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hi := chartRoot_sq q hq1 i
  have hj := chartRoot_sq q hq1 j
  have hn := norm_sub_sq_real (orthographicChart q i) (orthographicChart q j)
  rw [nearest_chart_chart_unit q hq1 i,nearest_chart_chart_unit q hq1 j] at hn
  have he : inner ℝ (orthographicChart q i) (orthographicChart q j)=
      chartRoot q i*chartRoot q j*packingHeight+
      chartRoot q i*inner ℝ (packingReference i) (tangentVector q j)+
      chartRoot q j*inner ℝ (packingReference j) (tangentVector q i)+
      inner ℝ (tangentVector q i) (tangentVector q j) := by
    simp only [orthographicChart,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial,hc]
    rw [real_inner_comm (tangentVector q i) (packingReference j)]
    dsimp [chartRoot]
    ring
  rw [he] at hn
  dsimp [contactDelta,squaredDistance,tau,contactLinear,contactQuadratic,contactRemainder]
  linear_combination hn-packingHeight*hi-packingHeight*hj

#check contact_taylor_exact_expansion
#print axioms contact_taylor_exact_expansion
end Blueprint.Thomson.Tail.Implementation
