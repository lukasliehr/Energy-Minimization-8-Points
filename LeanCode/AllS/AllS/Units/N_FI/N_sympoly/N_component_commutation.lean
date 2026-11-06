import AllS.Units.N_FI.N_sympoly.N_monomial_grade
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
namespace Blueprint.Thomson.Finite

theorem sympoly_component_commutation (p : Poly3) (n : ℕ) :
  invariantSubst (MvPolynomial.weightedHomogeneousComponent invariantWeight n p) =
    MvPolynomial.homogeneousComponent n (invariantSubst p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem
      (MvPolynomial.isWeightedHomogeneous_monomial invariantWeight d c rfl)]
    rw [MvPolynomial.homogeneousComponent_of_mem (sympoly_monomial_grade d c)]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]

#check sympoly_component_commutation
#print axioms sympoly_component_commutation
end Blueprint.Thomson.Finite
