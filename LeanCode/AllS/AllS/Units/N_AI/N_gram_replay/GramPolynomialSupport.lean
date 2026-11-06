import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport
import AllS.Units.N_AI.N_root_models.RootControlSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
open Polynomial

def bernsteinWeightPolynomial (d i : ℕ) : Polynomial ℝ :=
  C ((d.choose i:ℝ)/(2:ℝ)^d) * ((1+X)^i*(1-X)^(d-i))

theorem bernsteinWeightPolynomial_eval (d i : ℕ) (hi : i ≤ d) (x : ℝ) :
    (bernsteinWeightPolynomial d i).eval x = bernsteinWeight d i x := by
  simp only [bernsteinWeightPolynomial,bernsteinWeight,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_X,div_pow]
  have hd : (2:ℝ)^d = 2^i*2^(d-i) := by rw [←pow_add,Nat.add_sub_of_le hi]
  rw [hd]
  ring

theorem bernsteinWeightPolynomial_coeff (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    (bernsteinWeightPolynomial d i).coeff k =
      ((d.choose i:ℝ)*(d.choose k:ℝ)/(2:ℝ)^d) *
        (rationalBernsteinTransform d i k:ℝ) := by
  rw [rationalBernsteinTransform_cast d i k hi,bernsteinTransform_cast]
  simp only [bernsteinWeightPolynomial,Polynomial.coeff_C_mul]
  have hc : (d.choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp
  <;> ring

theorem bernsteinWeightPolynomial_natDegree (d i : ℕ) (hi : i ≤ d) :
    (bernsteinWeightPolynomial d i).natDegree ≤ d := by
  have hp : ((1+X:Polynomial ℝ)).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_add_le (1:Polynomial ℝ) X)
  have hm : ((1-X:Polynomial ℝ)).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_sub_le (1:Polynomial ℝ) X)
  calc
    _ ≤ (((1+X)^i*(1-X)^(d-i):Polynomial ℝ)).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((1+X:Polynomial ℝ)^i).natDegree+((1-X:Polynomial ℝ)^(d-i)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ i+(d-i) := Nat.add_le_add
      (by simpa using Polynomial.natDegree_pow_le_of_le i hp)
      (by simpa using Polynomial.natDegree_pow_le_of_le (d-i) hm)
    _ = d := Nat.add_sub_of_le hi

def gramPolynomial {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) (Polynomial ℝ) := fun i j =>
  C (δ*(K*K.transpose) i j) +
    ∑ u, C ((F u*(F u).transpose) i j)*bernsteinWeightPolynomial d u.val

theorem gramPolynomial_eval {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) (x : ℝ) (i j : Fin n) :
    (gramPolynomial δ K F i j).eval x = gramFromFactors δ K F x i j := by
  simp only [gramPolynomial,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_finsetSum,Polynomial.eval_mul,
    bernsteinWeightPolynomial_eval d _ (Nat.le_of_lt_succ (Fin.isLt _)),
    gramFromFactors,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem gramPolynomial_coeff {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : k ≤ d)
    (i j : Fin n) :
    (gramPolynomial δ K F i j).coeff k =
      (if k=0 then δ*(K*K.transpose) i j else 0) +
      ∑ u, (F u*(F u).transpose) i j *
        (((d.choose u.val:ℝ)*(d.choose k:ℝ)/(2:ℝ)^d) *
          (rationalBernsteinTransform d u.val k:ℝ)) := by
  simp only [gramPolynomial,Polynomial.coeff_add,Polynomial.coeff_C,
    Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    bernsteinWeightPolynomial_coeff d _ k (Nat.le_of_lt_succ (Fin.isLt _)) hk]

theorem gramPolynomial_natDegree {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (gramPolynomial δ K F i j).natDegree ≤ d := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C _).le.trans (Nat.zero_le d)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro u _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (bernsteinWeightPolynomial_natDegree d u.val (Nat.le_of_lt_succ u.isLt))

def literalGramPolynomial (cell : Literals.Cell) (b : Literals.Block) :
    Matrix (Fin b.order) (Fin b.order) (Polynomial ℝ) :=
  gramPolynomial ((2:ℝ)^cell.floorExponent) (literalMetric b cell.metricBits)
    (fun j : Fin (cell.bernsteinDegree+1) => literalFactor b cell.factorBits j.val)

theorem literalGramPolynomial_eval (cell : Literals.Cell) (b : Literals.Block)
    (x : ℝ) (i j : Fin b.order) :
    (literalGramPolynomial cell b i j).eval x = literalGram cell b x i j :=
  gramPolynomial_eval _ _ _ x i j

#print axioms bernsteinWeightPolynomial_eval
#print axioms bernsteinWeightPolynomial_coeff
#print axioms bernsteinWeightPolynomial_natDegree
#print axioms gramPolynomial_eval
#print axioms gramPolynomial_coeff
#print axioms gramPolynomial_natDegree
#print axioms literalGramPolynomial_eval
end Blueprint.CAP
