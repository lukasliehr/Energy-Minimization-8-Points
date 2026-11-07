import AllS.Units.N_GI.N_boundary_annulus.N_lower
import AllS.Units.N_GI.N_boundary_annulus.N_sum_squares
import AllS.Units.N_GI.N_boundary_annulus.N_product_second_order
import AllS.Units.N_GI.N_boundary_polynomials.N_polynomial_model

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_cap_coefficient : (23/160:ℝ)<(1-√2/8)*(√2/8) := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hlo : (7/5:ℝ)<√2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  nlinarith [hs,hlo]

theorem boundary_annulus_upper_scalar (u : Fin 8 → ℝ) (hu : ∀i,0≤u i)
    (he : Finset.univ.prod (fun i=>1+u i)=(250/239:ℝ)^2)
    (hss : (∑i,(u i)^2)≤((1-√2/8)^2+(√2/8)^2)*(∑i,u i)^2) :
    (∑i,u i)<boundaryRho^2 := by
  have h2 := product_one_add_second_order Finset.univ u (fun i _=>hu i)
  rw [he] at h2
  have hb : 1+(∑i,u i)+(1-√2/8)*(√2/8)*(∑i,u i)^2≤(250/239:ℝ)^2 := by
    nlinarith [hss,h2]
  have hS : 0≤∑i,u i := Finset.sum_nonneg (fun i _=>hu i)
  have hcoef := mul_le_mul_of_nonneg_right boundary_cap_coefficient.le (sq_nonneg (∑i,u i))
  have hrel : 1+(∑i,u i)+(23/160)*(∑i,u i)^2≤(250/239:ℝ)^2 := by linarith
  by_contra hn
  have hge : boundaryRho^2≤∑i,u i := le_of_not_gt hn
  have hsq : (boundaryRho^2)^2≤(∑i,u i)^2 := by nlinarith [sq_nonneg (∑i,u i-boundaryRho^2)]
  have hr : (250/239:ℝ)^2<1+boundaryRho^2+(23/160)*(boundaryRho^2)^2 := by norm_num [boundaryRho]
  nlinarith [hrel,hge,hsq,hr]

theorem boundary_annulus_upper (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) : gnomonicSquareSum Y<boundaryRho^2 := by
  have hss := boundary_annulus_sum_squares Y hY hal hg
  apply boundary_annulus_upper_scalar (fun i=>‖gnomonicTangent Y i‖^2) (fun _=>sq_nonneg _)
    (boundary_annulus_product_equation Y hY hal hg).1
  simpa only [←pow_mul,show 2*2=4 from rfl,gnomonicSquareSum] using hss

#print axioms boundary_annulus_upper
end Blueprint.Thomson.Tail.Implementation
