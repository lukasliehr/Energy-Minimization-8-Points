import AllS.Units.N_AI.N_data.LiteralGramGates
import AllS.Units.N_AI.N_gram_replay.GramPolynomialSupport
import AllS.Units.N_AI.N_matrix_polynomials.ScalarMatrixSupport
import AllS.Units.N_AI.N_scalar_models.N_cauchy_low_high

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

theorem literalMetricQ_cast (b : Literals.Block) (bits : ℕ) (i j : Fin b.order) :
    (literalMetricQ b bits i j:ℝ) = literalMetric b bits i j := by
  unfold literalMetricQ literalMetric
  split_ifs <;> push_cast <;> rfl

theorem literalFactorQ_cast (b : Literals.Block) (bits k : ℕ) (i j : Fin b.order) :
    (literalFactorQ b bits k i j:ℝ) = literalFactor b bits k i j := by
  unfold literalFactorQ literalFactor
  split_ifs <;> push_cast <;> rfl

theorem literalGramCoeffQ_cast (cell : Literals.Cell) (b : Literals.Block)
    (k : ℕ) (i j : Fin b.order) :
    (literalGramCoeffQ cell b k i j:ℝ) = (literalGramPolynomial cell b i j).coeff k := by
  by_cases hk : k ≤ cell.bernsteinDegree
  · rw [literalGramPolynomial,gramPolynomial_coeff _ _ _ k hk]
    simp only [literalGramCoeffQ,Matrix.mul_apply,Matrix.transpose_apply,
      Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_zpow,
      Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,apply_ite,Rat.cast_zero,
      literalMetricQ_cast,literalFactorQ_cast]
  · have hz : cell.bernsteinDegree.choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
    have hn : k≠0 := by omega
    have hd := gramPolynomial_natDegree ((2:ℝ)^cell.floorExponent)
      (literalMetric b cell.metricBits)
      (fun u : Fin (cell.bernsteinDegree+1) => literalFactor b cell.factorBits u.val) i j
    have hc : (literalGramPolynomial cell b i j).coeff k=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega))
    simp [literalGramCoeffQ,hz,hn,hc]

theorem polynomial_eq_finitePolynomial_of_natDegree (P : Polynomial ℝ) (N : ℕ)
    (hN : P.natDegree ≤ N) :
    finitePolynomial (fun k : Fin (N+1) => P.coeff k.val)=P := by
  ext k
  rw [finitePolynomial_coeff]
  by_cases hk : k < N+1
  · rw [dif_pos hk]
  · rw [dif_neg hk,Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem polynomial_eval_eq_scalarEval_of_natDegree (P : Polynomial ℝ) (N : ℕ)
    (hN : P.natDegree ≤ N) (x : ℝ) :
    P.eval x=scalarEval (fun k : Fin (N+1) => P.coeff k.val) x := by
  have he := congrArg (fun p : Polynomial ℝ => p.eval x)
    (polynomial_eq_finitePolynomial_of_natDegree P N hN)
  simpa only [finitePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    scalarEval] using he.symm

/-- The fixed coefficient witness is the actual source Gram polynomial. Thus
this operation produces zero analytic remainder rather than choosing a new
coefficient for each parameter value. -/
theorem literalGram_model {N : ℕ} (cell : Literals.Cell) (b : Literals.Block)
    (R : QMatrixModel N b.order b.order) (hN : cell.bernsteinDegree ≤ N)
    (he : ∀ i j, 0 ≤ R.error i j)
    (hc : ∀ k i j, (R.coeff k i j).lo ≤ literalGramCoeffQ cell b k.val i j ∧
      literalGramCoeffQ cell b k.val i j ≤ (R.coeff k i j).hi) :
    R.asMatrixTM.Valid (literalGram cell b) := by
  refine ⟨he,(fun k i j => (literalGramPolynomial cell b i j).coeff k.val),?_,?_⟩
  · intro k i j
    change ((R.coeff k i j).lo:ℝ) ≤ _ ∧ _ ≤ ((R.coeff k i j).hi:ℝ)
    have hh : ((R.coeff k i j).lo:ℝ) ≤ (literalGramCoeffQ cell b k.val i j:ℝ) ∧
        (literalGramCoeffQ cell b k.val i j:ℝ) ≤ ((R.coeff k i j).hi:ℝ) := by
      exact_mod_cast hc k i j
    simpa only [literalGramCoeffQ_cast cell b k.val i j] using hh
  · intro x hx i j
    have hd : (literalGramPolynomial cell b i j).natDegree ≤ N :=
      (gramPolynomial_natDegree ((2:ℝ)^cell.floorExponent)
      (literalMetric b cell.metricBits)
      (fun u : Fin (cell.bernsteinDegree+1) => literalFactor b cell.factorBits u.val) i j).trans hN
    have hev := polynomial_eval_eq_scalarEval_of_natDegree
      (literalGramPolynomial cell b i j) N hd x
    have hz : literalGram cell b x i j =
        matrixEval (fun k : Fin (N+1) => fun i j =>
          (literalGramPolynomial cell b i j).coeff k.val) x i j :=
      (literalGramPolynomial_eval cell b x i j).symm.trans hev
    change |literalGram cell b x i j-matrixEval _ x i j| ≤ (R.error i j:ℝ)
    rw [hz]
    rw [sub_self,abs_zero]
    exact_mod_cast he i j

#print axioms literalMetricQ_cast
#print axioms literalFactorQ_cast
#print axioms literalGramCoeffQ_cast
#print axioms literalGram_model
end Blueprint.CAP
