import AllS.Units.N_GI.N_boundary_polynomials.N_sqrt_majorant
import AllS.Units.N_GI.N_product_slice.N_gnomonic_inverse

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_gnomonic_quadratic (P Q t v Y Z : Point) (a b : ℝ)
    (hPQ : inner ℝ P Q=a) (hc : 0≤a+b/2)
    (hY : Y=(√(1+‖t‖^2))⁻¹ • (P+t))
    (hZ : Z=(√(1+‖v‖^2))⁻¹ • (Q+v))
    (hbound : inner ℝ Y Z≤a+b/2) :
    0≤b-2*(inner ℝ P v+inner ℝ Q t)+(a+b/2)*(‖t‖^2+‖v‖^2)-2*inner ℝ t v := by
  have ht : 0<√(1+‖t‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hv : 0<√(1+‖v‖^2) := Real.sqrt_pos.mpr (by positivity)
  have he : inner ℝ Y Z*(√(1+‖t‖^2)*√(1+‖v‖^2))=
      a+inner ℝ P v+inner ℝ Q t+inner ℝ t v := by
    rw [hY,hZ]
    simp only [inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,
      inner_add_left,inner_add_right,hPQ,real_inner_comm t Q]
    field_simp
    ring
  have h1 := mul_le_mul_of_nonneg_right hbound (mul_nonneg ht.le hv.le)
  rw [he] at h1
  have h2 := mul_le_mul_of_nonneg_left
    (boundary_sqrt_product_majorant (‖t‖^2) (‖v‖^2) (sq_nonneg _) (sq_nonneg _)) hc
  linarith

#print axioms boundary_gnomonic_quadratic
end Blueprint.Thomson.Tail.Implementation
