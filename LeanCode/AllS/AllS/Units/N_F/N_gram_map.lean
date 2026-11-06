import AllS.Units.N_FI.N_gram_map.N_family_and_map
import AllS.Units.N_FI.N_gram_map.N_linear_degree
import AllS.Units.N_FI.N_gram_map.N_physical_entries

namespace Blueprint.Thomson.Finite

theorem gram_polynomial : GramFamilyMapContract ∧ GramLinearDegreeContract ∧ GramPhysicalEntryContract :=
  ⟨gram_map_family_and_map,gram_map_linear_degree,gram_map_physical_entries⟩

#check gram_polynomial
#print axioms gram_polynomial
end Blueprint.Thomson.Finite
