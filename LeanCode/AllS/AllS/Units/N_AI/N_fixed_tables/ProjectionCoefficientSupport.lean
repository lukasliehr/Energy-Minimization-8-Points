import AllS.Units.N_AI.N_fixed_tables.InvariantProjectionSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem coordinateMonomial_monomial (t : Tag) :
    coordinateMonomial t=MvPolynomial.monomial (tagExponent t) (1:ℝ) := by
  have he : Finsupp.single (0:Fin 3) t.1+Finsupp.single 1 t.2.1+
      Finsupp.single 2 t.2.2=tagExponent t := by
    ext i
    fin_cases i <;> simp [tagExponent,Finsupp.single_apply]
  simpa only [coordinateMonomial,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul,mul_one] using
    congrArg (fun e : Fin 3 →₀ ℕ => MvPolynomial.monomial e (1:ℝ)) he

theorem coefficient_coordinateMonomial (t u : Tag) :
    MvPolynomial.coeff (tagExponent t) (coordinateMonomial u)=if u=t then 1 else 0 := by
  rw [coordinateMonomial_monomial,MvPolynomial.coeff_monomial]
  simp only [tagExponent_injective.eq_iff]

theorem coefficient_invariantCoordinateColumn {n : ℕ} (t : Tag)
    (tags : Fin n → Tag) (v : Fin n → ℝ) :
    MvPolynomial.coeff (tagExponent t) (invariantCoordinateColumn tags v)=
      ∑ i,if tags i=t then v i else 0 := by
  classical
  simp only [invariantCoordinateColumn,MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul,coefficient_coordinateMonomial]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

#print axioms coefficient_coordinateMonomial
#print axioms coefficient_invariantCoordinateColumn
end Blueprint.Thomson.Finite
