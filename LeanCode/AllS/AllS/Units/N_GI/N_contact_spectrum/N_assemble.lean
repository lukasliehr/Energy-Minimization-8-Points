import AllS.Units.N_GI.N_contact_spectrum.N_fourier_rows
import AllS.Units.N_GI.N_contact_spectrum.N_rotation_kernel
import AllS.Units.N_GI.N_contact_spectrum.N_physical_weighted
import AllS.Units.N_GI.N_contact_spectrum.N_stress_zero

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_spectrum_assemble :
    (∀ q : TangentCoordinates, q∈rotationSlice →
      (59546/15625)*‖q‖^2 ≤ ∑ e : ContactIndex, contactWeight e*(contactLinear q e.1 (contactNext e))^2) ∧
    (∀ q : TangentCoordinates, q∈rotationSlice →
      3*‖q‖^2 ≤ ∑ e : ContactIndex, (contactLinear q e.1 (contactNext e))^2) ∧
    (∀ q : TangentCoordinates, (∑ e : ContactIndex, contactWeight e*contactLinear q e.1 (contactNext e))=0) ∧
    (∀ (w : ℝ) (j k : Fin 13),
      contactGram w (contactRawVector j) (contactRawVector k)=contactGramEntry w j k) ∧
    (∀ q : TangentCoordinates,
      (∀ e : ContactIndex, contactLinear q e.1 (contactNext e)=0) ↔ q=rotationProjection q) :=
  ⟨contact_spectrum_physical_weighted,contact_spectrum_physical_unweighted,
    contact_spectrum_stress_zero,contactGram_raw,contactLinear_kernel⟩

#print axioms contact_spectrum_assemble
end Blueprint.Thomson.Tail.Implementation
