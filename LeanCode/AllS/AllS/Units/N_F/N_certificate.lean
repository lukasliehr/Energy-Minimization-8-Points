import AllS.Units.N_FI.N_certificate.N_typed_contract
import AllS.Units.N_FI.N_certificate.N_balanced_target

namespace Blueprint.Thomson.Finite

theorem finite_certificate_definition : CertificateTypedContract ∧ BalancedTargetContract :=
  ⟨certificate_typed_contract,certificate_balanced_target⟩

#check Certificate
#print axioms Certificate
#check finite_certificate_definition
#print axioms finite_certificate_definition
end Blueprint.Thomson.Finite
