import AllS.Units.N_GI.N_product_slice.N_alignment

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem product_slice_assemble (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) :
    (∀i,0<productFactor Y i ∧ inner ℝ (packingReference i) (gnomonicTangent Y i)=0 ∧
      productFactor Y i=1/√(1+‖gnomonicTangent Y i‖^2) ∧
      Y i=(√(1+‖gnomonicTangent Y i‖^2))⁻¹ • (packingReference i+gnomonicTangent Y i)) ∧
    (∑i,crossVec (packingReference i) (gnomonicTangent Y i))=0 := by
  refine ⟨fun i => ?_,product_slice_slice_stationarity Y hal hp⟩
  have hp := product_slice_positive_factors Y hal hp i
  exact ⟨hp.1,hp.2,gnomonic_inverse Y hY i hp.1⟩

#print axioms product_slice_assemble
end Blueprint.Thomson.Tail.Implementation
