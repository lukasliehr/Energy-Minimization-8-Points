import AllS.Units.N_GI.N_product_slice.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation
theorem product_slice (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) :
    (∀i,0<productFactor Y i ∧ inner ℝ (packingReference i) (gnomonicTangent Y i)=0 ∧
      productFactor Y i=1/√(1+‖gnomonicTangent Y i‖^2) ∧
      Y i=(√(1+‖gnomonicTangent Y i‖^2))⁻¹ • (packingReference i+gnomonicTangent Y i)) ∧
    (∑i,crossVec (packingReference i) (gnomonicTangent Y i))=0 := Implementation.product_slice_assemble Y hY hal hp

#print axioms product_slice
end Blueprint.Thomson.Tail
