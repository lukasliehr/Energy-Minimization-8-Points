import AllS.Units.N_FI.N_energy_lower.N_summed_certificate
import AllS.Units.N_FI.N_energy_lower.N_energy_bound
import AllS.Units.N_FI.N_energy_lower.N_equality_zeros

namespace Blueprint.Thomson.Finite

theorem certificate_energy_lower : SummedCertificateContract ∧ EnergyLowerContract ∧ EqualityZerosContract :=
  ⟨energy_lower_summed_certificate,energy_lower_energy_bound,energy_lower_equality_zeros⟩

#check certificate_energy_lower
#print axioms certificate_energy_lower
end Blueprint.Thomson.Finite
