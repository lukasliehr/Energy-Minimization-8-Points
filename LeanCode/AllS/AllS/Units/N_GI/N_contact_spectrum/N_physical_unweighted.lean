import AllS.Units.N_GI.N_contact_spectrum.N_physical_bound

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_spectrum_physical_unweighted (q : TangentCoordinates) (hq : q∈rotationSlice) :
    3*‖q‖^2 ≤ ∑ e : ContactIndex, (contactLinear q e.1 (contactNext e))^2 := by
  have h := contactGram_slice_bound 1 3 contact_spectrum_unweighted_conditions q hq
  simpa [contactGram,pow_two] using h

#print axioms contact_spectrum_physical_unweighted
end Blueprint.Thomson.Tail.Implementation
