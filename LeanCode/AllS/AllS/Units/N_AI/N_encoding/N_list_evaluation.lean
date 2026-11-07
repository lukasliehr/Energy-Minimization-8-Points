import AllS.Units.N_AI.N_data.N_polynomial_list
import Pilot.BalancedProof
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def EncodingListEvaluationStatement : Prop :=
  ∀ (L : List ℤ) (B : ℤ), BalancedProof.encode B L = (listPolynomial L).eval B
theorem listPolynomial_nil {R : Type*} [Semiring R] :
    listPolynomial ([] : List R) = 0 := by simp [listPolynomial]

theorem listPolynomial_cons {R : Type*} [Semiring R] (a : R) (L : List R) :
    listPolynomial (a::L) = Polynomial.C a + Polynomial.X * listPolynomial L := by
  classical
  simp [listPolynomial, Fin.sum_univ_succ, Finset.mul_sum, Polynomial.X_mul_monomial]

theorem encoding_list_evaluation : EncodingListEvaluationStatement := by
  intro L B
  induction L with
  | nil => simp [BalancedProof.encode, listPolynomial_nil]
  | cons a L ih =>
    rw [BalancedProof.encode, listPolynomial_cons]
    simp [ih]

#check encoding_list_evaluation
#print encoding_list_evaluation
#print axioms encoding_list_evaluation
#print axioms listPolynomial_cons
end Blueprint.CAP
