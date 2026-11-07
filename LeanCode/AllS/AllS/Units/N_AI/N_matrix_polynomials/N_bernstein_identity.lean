import AllS.Units.N_AI.N_data.N_polynomial_list
import Mathlib.RingTheory.Polynomial.Bernstein

noncomputable section
open scoped BigOperators
open Polynomial
namespace Blueprint.CAP

def bernsteinTransform (d i k : ℕ) : ℚ :=
  (((1+X)^i*(1-X)^(d-i) : Polynomial ℚ).coeff k)/(d.choose k:ℚ)

def bernsteinWeight (d i : ℕ) (x : ℝ) : ℝ :=
  (d.choose i:ℝ)*((1+x)/2)^i*((1-x)/2)^(d-i)

def MatrixBernsteinIdentityStatement : Prop :=
  ∀ (d : ℕ) (a : Fin (d+1)→ℝ) (x : ℝ),
    scalarEval a x=
      ∑ i : Fin (d+1), (∑ k : Fin (d+1), (bernsteinTransform d i.val k.val:ℝ)*a k)*
        bernsteinWeight d i.val x

theorem affinePolynomial_coeff (a b : ℝ) (d k : ℕ) :
    ((C a*X+C b)^d : Polynomial ℝ).coeff k=(d.choose k:ℝ)*a^k*b^(d-k) := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  have ht (j : ℕ) : (((C a*X)^j*(C b)^(d-j)*(d.choose j:Polynomial ℝ))).coeff k=
      if j=k then (d.choose j:ℝ)*a^j*b^(d-j) else 0 := by
    simp only [mul_pow, ←C_pow, Polynomial.coeff_mul_natCast, Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all <;> ring
  simp only [ht]
  by_cases hk : k<d+1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp [hk]
  · have hc : d.choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [Finset.sum_eq_zero]
    · simp [hc]
    · intro j hj
      have hjk : j≠k := by intro h; subst j; exact hk (Finset.mem_range.mp hj)
      simp [hjk]

theorem bernsteinTransform_cast (d i k : ℕ) :
    (bernsteinTransform d i k:ℝ)=
      (((1+X)^i*(1-X)^(d-i) : Polynomial ℝ).coeff k)/(d.choose k:ℝ) := by
  have hm : (((1+X)^i*(1-X)^(d-i) : Polynomial ℚ).map (algebraMap ℚ ℝ))=
      ((1+X)^i*(1-X)^(d-i) : Polynomial ℝ) := by simp
  have hc := congrArg (fun p : Polynomial ℝ=>p.coeff k) hm
  simp only [Polynomial.coeff_map] at hc
  change ((((1+X)^i*(1-X)^(d-i) : Polynomial ℚ).coeff k:ℚ):ℝ)=
    ((1+X)^i*(1-X)^(d-i) : Polynomial ℝ).coeff k at hc
  unfold bernsteinTransform
  push_cast
  rw [hc]

theorem one_sub_X_pow_coeff (d k : ℕ) :
    ((1-X)^d : Polynomial ℝ).coeff k=(d.choose k:ℝ)*(-1)^k := by
  simpa only [map_neg, C_1, neg_one_mul, one_pow, mul_one, sub_eq_add_neg, add_comm]
    using affinePolynomial_coeff (-1) 1 d k

theorem bernsteinTransform_formula (d i k : ℕ) :
    (bernsteinTransform d i k:ℝ)=
      (∑ j∈Finset.range (k+1), (-1:ℝ)^(k-j)*(i.choose j:ℝ)*((d-i).choose (k-j):ℝ)) /
        (d.choose k:ℝ) := by
  rw [bernsteinTransform_cast, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.coeff_one_add_X_pow, one_sub_X_pow_coeff]
  ring

theorem bernsteinTransform_source_formula (d i k : ℕ) (hi : i ≤ d) :
    (bernsteinTransform d i k:ℝ)=
      (∑ j∈Finset.Icc (k+i-d) (min i k),
        (-1:ℝ)^(k-j)*(i.choose j:ℝ)*((d-i).choose (k-j):ℝ)) /
        (d.choose k:ℝ) := by
  rw [bernsteinTransform_formula]
  congr 1
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hj hn
    simp only [Finset.mem_range, Finset.mem_Icc] at hj hn
    by_cases hji : j ≤ i
    · have hkji : d-i<k-j := by omega
      rw [Nat.choose_eq_zero_of_lt hkji, Nat.cast_zero, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hji), Nat.cast_zero, mul_zero, zero_mul]

theorem bernstein_generating (d : ℕ) (x : ℝ) :
    (∑ i∈Finset.range (d+1), C (bernsteinWeight d i x)*((1+X)^i*(1-X)^(d-i)) : Polynomial ℝ)=
      (1+C x*X)^d := by
  let z : ℝ := (1+x)/2
  let w : ℝ := (1-x)/2
  have ha : C z*(1+X)+C w*(1-X)=(1+C x*X : Polynomial ℝ) := by
    calc
      _ = C (z+w)+C (z-w)*X := by rw [map_add,map_sub]; ring
      _ = _ := by rw [show z+w=1 by dsimp [z,w]; ring,
        show z-w=x by dsimp [z,w]; ring, C_1]
  rw [←ha, add_pow]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bernsteinWeight, map_mul, map_pow, map_natCast, mul_pow]
  change (d.choose i:Polynomial ℝ)*(C z)^i*(C w)^(d-i)*((1+X)^i*(1-X)^(d-i))=_
  ring

theorem bernstein_monomial (d k : ℕ) (hk : k ≤ d) (x : ℝ) :
    x^k=∑ i : Fin (d+1), (bernsteinTransform d i.val k:ℝ)*bernsteinWeight d i.val x := by
  have hg := congrArg (fun p : Polynomial ℝ=>p.coeff k) (bernstein_generating d x)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at hg
  have ha : ((1+C x*X)^d : Polynomial ℝ).coeff k=(d.choose k:ℝ)*x^k := by
    simpa only [C_1, one_pow, mul_one, add_comm] using affinePolynomial_coeff x 1 d k
  rw [ha] at hg
  have hchoose : (d.choose k:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  calc
    x^k=((d.choose k:ℝ)*x^k)/(d.choose k:ℝ) := by field_simp
    _ = (∑ i∈Finset.range (d+1), bernsteinWeight d i x*
        ((1+X)^i*(1-X)^(d-i) : Polynomial ℝ).coeff k)/(d.choose k:ℝ) := by rw [hg]
    _ = ∑ i : Fin (d+1), (bernsteinTransform d i.val k:ℝ)*bernsteinWeight d i.val x := by
      rw [Finset.sum_div, ←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rw [bernsteinTransform_cast]
      ring

theorem matrix_polynomials_bernstein_identity : MatrixBernsteinIdentityStatement := by
  intro d a x
  unfold scalarEval
  simp_rw [bernstein_monomial d _ (Nat.le_of_lt_succ (Fin.isLt _)) x]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem bernsteinWeight_nonneg (d i : ℕ) (x : ℝ) (hx : x∈cellDomain) :
    0 ≤ bernsteinWeight d i x := by
  unfold bernsteinWeight
  have hz : 0 ≤ (1+x)/2 := by rcases hx with ⟨hl,hu⟩; linarith
  have hw : 0 ≤ (1-x)/2 := by rcases hx with ⟨hl,hu⟩; linarith
  positivity

theorem bernsteinWeight_sum (d : ℕ) (x : ℝ) :
    ∑ i : Fin (d+1), bernsteinWeight d i.val x=1 := by
  have hs := congrArg (fun p : Polynomial ℝ=>p.eval ((1+x)/2)) (bernsteinPolynomial.sum ℝ d)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_one] at hs
  rw [←Fin.sum_univ_eq_sum_range] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [bernsteinWeight, bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  congr 2
  ring

#check matrix_polynomials_bernstein_identity
#print MatrixBernsteinIdentityStatement
#print axioms matrix_polynomials_bernstein_identity
#print axioms affinePolynomial_coeff
#print axioms bernstein_generating
#print axioms bernsteinTransform_source_formula
#print axioms bernsteinWeight_nonneg
#print axioms bernsteinWeight_sum
end Blueprint.CAP
