import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_zero_jets_divisible
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem newton_hermite_unique (n : ℕ) (z : Fin n → ℝ) (m : Fin n → ℕ)
    (P Q : Polynomial ℝ) (hz : Function.Injective z)
    (hP : P.degree < (∑ i, m i)) (hQ : Q.degree < (∑ i, m i))
    (hjets : ∀ i j, j < m i → ((Polynomial.derivative^[j]) P).eval (z i) =
      ((Polynomial.derivative^[j]) Q).eval (z i)) : P = Q := by
  classical
  let W : Polynomial ℝ := ∏ i, (Polynomial.X-Polynomial.C (z i))^(m i)
  have hdiv : W ∣ P-Q := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (Polynomial.pairwise_coprime_X_sub_C hz hij).pow
    · intro i
      apply newton_hermite_zero_jets_divisible
      intro j hj
      rw [Polynomial.iterate_derivative_sub, Polynomial.eval_sub, hjets i j hj, sub_self]
  have hdegW : W.degree = (∑ i, m i) := by
    dsimp [W]
    rw [Polynomial.degree_prod_of_monic]
    · simp [Polynomial.degree_pow]
    · intro i hi
      exact (Polynomial.monic_X_sub_C (z i)).pow (m i)
  have hdegR : (P-Q).degree < (∑ i, m i) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le P Q) (max_lt hP hQ)
  apply sub_eq_zero.mp
  by_contra h
  have hle := Polynomial.degree_le_of_dvd hdiv h
  rw [hdegW] at hle
  exact (not_lt_of_ge hle) hdegR

#check newton_hermite_unique
#print axioms newton_hermite_unique
end Blueprint.Thomson.Finite
