import AllS.Units.N_G.N_product_slice
import AllS.Units.N_G.N_slice_point_bound
import AllS.Units.N_GI.N_nearest_chart.N_orthogonal_slice

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def gnomonicCoordinates (Y : Fin 8 → Point) : TangentCoordinates := inverseCoordinates (gnomonicTangent Y)
def gnomonicSquareSum (Y : Fin 8 → Point) : ℝ := ∑i,‖gnomonicTangent Y i‖^2

theorem gnomonicCoordinates_tangent (Y : Fin 8 → Point) (hal : IsProductAligned Y)
    (hp : 0<productGauge Y) (i : Fin 8) : tangentVector (gnomonicCoordinates Y) i=gnomonicTangent Y i := by
  rw [gnomonicCoordinates,inverseCoordinates_tangent]
  have h := (product_slice_positive_factors Y hal hp i).2
  simpa [SquareAntiprismVerification.inverseSphereChart,real_inner_comm,h]

theorem gnomonicCoordinates_mem_slice (Y : Fin 8 → Point) (hal : IsProductAligned Y)
    (hp : 0<productGauge Y) : gnomonicCoordinates Y∈rotationSlice :=
  inverseCoordinates_mem_rotationSlice _ (product_slice_slice_stationarity Y hal hp)

theorem gnomonicCoordinates_norm_sq (Y : Fin 8 → Point) (hal : IsProductAligned Y)
    (hp : 0<productGauge Y) : ‖gnomonicCoordinates Y‖^2=gnomonicSquareSum Y := by
  rw [←tangentVector_sum_norm_sq]
  simp only [gnomonicCoordinates_tangent Y hal hp,gnomonicSquareSum]

theorem boundary_annulus_product_equation (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) :
    (Finset.univ.prod (fun i : Fin 8 => 1+‖gnomonicTangent Y i‖^2))=(250/239:ℝ)^2 ∧
    ∀i,‖gnomonicTangent Y i‖^2≤(1-√2/8)*gnomonicSquareSum Y := by
  have hp : 0<productGauge Y := by rw [hg]; norm_num
  have hfac : productGauge Y=Finset.univ.prod (fun i : Fin 8 => productFactor Y i) := by
    rw [productGauge_aligned_value Y hal]
    apply Finset.prod_congr rfl
    intro i _
    exact max_eq_left (product_slice_positive_factors Y hal hp i).1.le
  have hs (i : Fin 8) : (1+‖gnomonicTangent Y i‖^2)*(productFactor Y i)^2=1 := by
    rw [(gnomonic_inverse Y hY i (product_slice_positive_factors Y hal hp i).1).1]
    have hn : √(1+‖gnomonicTangent Y i‖^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
    exact (Real.sq_sqrt (by positivity)).symm
  have hprod : (Finset.univ.prod (fun i : Fin 8 => 1+‖gnomonicTangent Y i‖^2))*(productGauge Y)^2=1 := by
    rw [hfac,←Finset.prod_pow,←Finset.prod_mul_distrib]
    simp only [hs,Finset.prod_const_one]
  constructor
  · rw [hg] at hprod
    nlinarith [hprod]
  · intro i
    have h := slice_point_bound_assemble (gnomonicCoordinates Y) (gnomonicCoordinates_mem_slice Y hal hp) i
    simpa only [gnomonicCoordinates_tangent Y hal hp,gnomonicSquareSum] using h

#print axioms boundary_annulus_product_equation
end Blueprint.Thomson.Tail.Implementation
