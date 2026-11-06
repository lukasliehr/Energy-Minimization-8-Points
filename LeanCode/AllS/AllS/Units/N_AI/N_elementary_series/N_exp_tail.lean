import Blueprint.CAPContracts
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def expTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), x^k/(Nat.factorial k : ℝ)
def ExpTailStatement : Prop :=
  ∀ (x : ℝ) (n : ℕ), 0≤x → x<(n:ℝ)+2 →
    expTaylor n x ≤ Real.exp x ∧
    Real.exp x ≤ expTaylor n x +
      (x^(n+1)/(Nat.factorial (n+1):ℝ))/(1-x/((n:ℝ)+2))
theorem real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' k : ℕ, x^k/(Nat.factorial k:ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem exp_tail_term_bound (x : ℝ) (m j : ℕ) (hx : 0≤x) :
    x^(j+m)/(Nat.factorial (j+m):ℝ) ≤
      (x^m/(Nat.factorial m:ℝ)) * (x/((m:ℝ)+1))^j := by
  have hf : (Nat.factorial m:ℝ)*((m:ℝ)+1)^j ≤ (Nat.factorial (m+j):ℝ) := by
    exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m:=m) (n:=j))
  calc
    x^(j+m)/(Nat.factorial (j+m):ℝ) = x^(m+j)/(Nat.factorial (m+j):ℝ) := by rw [Nat.add_comm j m]
    _ ≤ x^(m+j)/((Nat.factorial m:ℝ)*((m:ℝ)+1)^j) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity) hf
    _ = (x^m/(Nat.factorial m:ℝ)) * (x/((m:ℝ)+1))^j := by
      simp only [pow_add, div_pow, div_eq_mul_inv, mul_inv_rev]
      ring

theorem expTail_general : ExpTailStatement := by
  intro x n hx hxupper
  let m := n+1
  let r := x/((m:ℝ)+1)
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r<1 := by
    dsimp [r, m]
    rw [div_lt_one (by positivity)]
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hxupper
  have hr : |r|<1 := by rwa [abs_of_nonneg hr0]
  have hs : Summable (fun k : ℕ => x^k/(Nat.factorial k:ℝ)) :=
    NormedSpace.expSeries_div_summable x
  have htail : Summable (fun j : ℕ => x^(j+m)/(Nat.factorial (j+m):ℝ)) :=
    (summable_nat_add_iff m).2 hs
  have hg : Summable (fun j : ℕ => r^j) := summable_geometric_of_abs_lt_one hr
  have hsplit := hs.sum_add_tsum_nat_add m
  rw [← real_exp_eq_tsum] at hsplit
  have htail0 : 0 ≤ ∑' j : ℕ, x^(j+m)/(Nat.factorial (j+m):ℝ) :=
    tsum_nonneg (fun j => by positivity)
  have htailbound : (∑' j : ℕ, x^(j+m)/(Nat.factorial (j+m):ℝ)) ≤
      (x^m/(Nat.factorial m:ℝ))/(1-r) := by
    calc
      _ ≤ ∑' j : ℕ, (x^m/(Nat.factorial m:ℝ))*r^j :=
        htail.tsum_le_tsum (fun j => exp_tail_term_bound x m j hx)
          (hg.mul_left (x^m/(Nat.factorial m:ℝ)))
      _ = (x^m/(Nat.factorial m:ℝ))/(1-r) := by
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr]
        rfl
  constructor
  · change (∑ k ∈ Finset.range m, x^k/(Nat.factorial k:ℝ)) ≤ Real.exp x
    linarith
  · have h : Real.exp x ≤ expTaylor n x + (x^m/(Nat.factorial m:ℝ))/(1-r) := by
      change Real.exp x ≤ (∑ k ∈ Finset.range m, x^k/(Nat.factorial k:ℝ)) + _
      linarith
    simpa [m, r, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

theorem elementary_series_exp_tail (x : ℝ) (n : ℕ) (hx : 0≤x) (hxu : x≤1/8) :
    expTaylor n x ≤ Real.exp x ∧
    Real.exp x ≤ expTaylor n x +
      (x^(n+1)/(Nat.factorial (n+1):ℝ))/(1-x/((n:ℝ)+2)) := by
  apply expTail_general x n hx
  have : (0:ℝ)≤n := Nat.cast_nonneg n
  linarith
#check elementary_series_exp_tail
#print ExpTailStatement
#print axioms elementary_series_exp_tail
#print axioms expTail_general
end Blueprint.CAP
