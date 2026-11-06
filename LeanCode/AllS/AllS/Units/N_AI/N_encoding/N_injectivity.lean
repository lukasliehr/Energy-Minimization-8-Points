import AllS.Units.N_AI.N_encoding.N_list_evaluation
import Pilot.SharedPolynomialProof
import Blueprint.Target

namespace Blueprint.CAP
def EncodingInjectivityStatement : Prop :=
  ∀ (u v : List ℤ) (H : ℤ), 0<H → u.length=v.length →
    (∀ x∈u, -H≤x ∧ x<H) → (∀ x∈v, -H≤x ∧ x<H) →
    BalancedProof.encode (2*H) u = BalancedProof.encode (2*H) v →
    u=v ∧ listPolynomial u=listPolynomial v
theorem encoding_injectivity : EncodingInjectivityStatement := by
  intro u v H hH hlen hu hv heq
  have h := SharedPolynomialProof.bounded_encoding_injective H hH u v hu hv hlen heq
  exact ⟨h, congrArg listPolynomial h⟩
#check encoding_injectivity
#print encoding_injectivity
#print axioms encoding_injectivity
end Blueprint.CAP
