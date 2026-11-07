import AllS.Units.N_GI.N_contact_spectrum.N_physical_bound

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_spectrum_physical_weighted (q : TangentCoordinates) (hq : q∈rotationSlice) :
    (59546/15625)*‖q‖^2 ≤ ∑ e : ContactIndex, contactWeight e*(contactLinear q e.1 (contactNext e))^2 := by
  have h := contactGram_slice_bound contactKappa (59546/15625) contact_spectrum_weighted_conditions q hq
  simpa [contactGram,contactWeight,pow_two,mul_assoc] using h

#print axioms contact_spectrum_physical_weighted
end Blueprint.Thomson.Tail.Implementation
