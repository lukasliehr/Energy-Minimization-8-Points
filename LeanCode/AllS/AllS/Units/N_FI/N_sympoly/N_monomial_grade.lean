import AllS.Units.N_FI.N_sympoly.N_elementary_bridge
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem sigma_homogeneous  : sigma.IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_X ℝ (0 : Fin 3)).add
    (MvPolynomial.isHomogeneous_X ℝ (1 : Fin 3))).add
      (MvPolynomial.isHomogeneous_X ℝ (2 : Fin 3))
#check sigma_homogeneous
#print axioms sigma_homogeneous

theorem e2_homogeneous  : e2.IsHomogeneous 2 := by
  have h (i : Fin 3) := MvPolynomial.isHomogeneous_X ℝ i
  exact ((h 0 |>.mul (h 1)).add (h 0 |>.mul (h 2))).add (h 1 |>.mul (h 2))
#check e2_homogeneous
#print axioms e2_homogeneous

theorem e3_homogeneous  : e3.IsHomogeneous 3 := by
  exact ((MvPolynomial.isHomogeneous_X ℝ (0 : Fin 3)).mul
    (MvPolynomial.isHomogeneous_X ℝ (1 : Fin 3))).mul
      (MvPolynomial.isHomogeneous_X ℝ (2 : Fin 3))
#check e3_homogeneous
#print axioms e3_homogeneous

theorem invariantWeight_eq (d : Fin 3 →₀ ℕ) : Finsupp.weight invariantWeight d = d 0 + 2 * d 1 + 3 * d 2 := by
  simp [Finsupp.weight_eq_sum, invariantWeight, Fin.sum_univ_succ,
    smul_eq_mul, mul_comm, add_assoc]
#check invariantWeight_eq
#print axioms invariantWeight_eq

theorem invariantSubst_monomial (d : Fin 3 →₀ ℕ) (c : ℝ) : invariantSubst (MvPolynomial.monomial d c) = MvPolynomial.C c * (sigma ^ d 0 * e2 ^ d 1 * e3 ^ d 2) := by
  rw [invariantSubst, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype d _ (fun i => pow_zero _)]
  simp [Fin.prod_univ_succ, MvPolynomial.algebraMap_eq, mul_assoc]
#check invariantSubst_monomial
#print axioms invariantSubst_monomial

theorem sympoly_monomial_grade (d : Fin 3 →₀ ℕ) (c : ℝ) : (invariantSubst (MvPolynomial.monomial d c)).IsHomogeneous (Finsupp.weight invariantWeight d) := by
  rw [invariantSubst_monomial, invariantWeight_eq]
  simpa only [one_mul] using
    (((sigma_homogeneous.pow (d 0)).mul (e2_homogeneous.pow (d 1))).mul
      (e3_homogeneous.pow (d 2))).C_mul c
#check sympoly_monomial_grade
#print axioms sympoly_monomial_grade
end Blueprint.Thomson.Finite
