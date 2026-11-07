import AllS.Units.N_GI.N_contact_spectrum.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem contact_spectrum :
    (∀ q : TangentCoordinates, q∈rotationSlice →
      (59546/15625)*‖q‖^2 ≤ ∑ e : ContactIndex, contactWeight e*(contactLinear q e.1 (contactNext e))^2) ∧
    (∀ q : TangentCoordinates, q∈rotationSlice →
      3*‖q‖^2 ≤ ∑ e : ContactIndex, (contactLinear q e.1 (contactNext e))^2) ∧
    (∀ q : TangentCoordinates, (∑ e : ContactIndex, contactWeight e*contactLinear q e.1 (contactNext e))=0) ∧
    (∀ (w : ℝ) (j k : Fin 13),
      contactGram w (contactRawVector j) (contactRawVector k)=contactGramEntry w j k) ∧
    (∀ q : TangentCoordinates,
      (∀ e : ContactIndex, contactLinear q e.1 (contactNext e)=0) ↔ q=rotationProjection q) :=
  contact_spectrum_assemble

#print axioms contact_spectrum
end Blueprint.Thomson.Tail
