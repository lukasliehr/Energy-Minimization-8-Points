import AllS.Units.N_FI.N_geometry.N_contact_cardinalities
import AllS.Units.N_FI.N_geometry.N_distance_domain
import AllS.Units.N_FI.N_geometry.N_energy_normalization
import AllS.Units.N_FI.N_geometry.N_gram_entries

noncomputable section
namespace Blueprint.Thomson.Finite

def CandidateGeometryContract : Prop :=
  (∀ a : ℝ, physical a → IsConfiguration (X a)) ∧
  CandidateGramContract ∧ ContactCardinalityContract ∧
  DistanceDomainContract ∧ EnergyNormalizationContract

theorem candidate_geometry : CandidateGeometryContract := by
  refine ⟨?_, geometry_gram_entries, geometry_contact_cardinalities,
    geometry_distance_domain, geometry_energy_normalization⟩
  intro a ha
  exact candidate_is_configuration a (physical_mem_Ioo a ha)

#check candidate_geometry
#print axioms candidate_geometry
#check CandidateGeometryContract
#print axioms CandidateGeometryContract
end Blueprint.Thomson.Finite
