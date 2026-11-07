import AllS.Units.N_GI.N_product_slice.N_positive_factors

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem gnomonic_inverse (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) (i : Fin 8)
    (hi : 0<productFactor Y i) :
    productFactor Y i=1/√(1+‖gnomonicTangent Y i‖^2) ∧
    Y i=(√(1+‖gnomonicTangent Y i‖^2))⁻¹ • (packingReference i+gnomonicTangent Y i) := by
  have hv : packingReference i+gnomonicTangent Y i=(productFactor Y i)⁻¹ • Y i := by
    unfold gnomonicTangent
    abel
  have hn : ‖packingReference i+gnomonicTangent Y i‖=(productFactor Y i)⁻¹ := by
    rw [hv,norm_smul,hY i,mul_one,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hi)]
  have hs : (productFactor Y i)⁻¹^2=1+‖gnomonicTangent Y i‖^2 := by
    have hh := norm_add_sq_real (packingReference i) (gnomonicTangent Y i)
    rw [hn,packingReference_norm,gnomonicTangent_orthogonal Y i hi] at hh
    simpa using hh
  have hsqrt : √(1+‖gnomonicTangent Y i‖^2)=(productFactor Y i)⁻¹ := by
    rw [←hs,Real.sqrt_sq (inv_nonneg.mpr hi.le)]
  constructor
  · rw [hsqrt,one_div,inv_inv]
  · rw [hsqrt,inv_inv,hv,smul_smul,mul_inv_cancel₀ hi.ne',one_smul]

theorem product_slice_gnomonic_inverse (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) :
    ∀i,productFactor Y i=1/√(1+‖gnomonicTangent Y i‖^2) ∧
      Y i=(√(1+‖gnomonicTangent Y i‖^2))⁻¹ • (packingReference i+gnomonicTangent Y i) :=
  fun i => gnomonic_inverse Y hY i (product_slice_positive_factors Y hal hp i).1

#print axioms product_slice_gnomonic_inverse
end Blueprint.Thomson.Tail.Implementation
