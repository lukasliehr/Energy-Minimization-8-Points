import Mathlib

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_polynomials_sqrt_majorant (u v : ℝ) (hu : 0≤u) (hv : 0≤v) :
    √((1+u)*(1+v))≤1+(u+v)/2 := by
  apply (Real.sqrt_le_left (by linarith)).mpr
  nlinarith [sq_nonneg (u-v)]

theorem boundary_sqrt_product_majorant (u v : ℝ) (hu : 0≤u) (hv : 0≤v) :
    √(1+u)*√(1+v)≤1+(u+v)/2 := by
  rw [←Real.sqrt_mul (by linarith : 0≤1+u)]
  exact boundary_polynomials_sqrt_majorant u v hu hv

#print axioms boundary_polynomials_sqrt_majorant
end Blueprint.Thomson.Tail.Implementation
