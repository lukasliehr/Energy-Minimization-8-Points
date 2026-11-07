import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_divided_difference_monomials
import Blueprint.FiniteDefinitions
import Blueprint.Target
import AllS.Units.N_FI.N_newton_hermite.N_basis_jet

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def polynomialJets (P : Polynomial ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.derivative^[k]) P).eval x

def polynomialDeflateBlock (z : ℕ → ℝ) (start : ℕ) : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, P => P
  | k+1, P => polynomialDeflate (z (start+k)) (polynomialDeflateBlock z start k P)

def polynomialDD (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ) : ℝ :=
  (polynomialDeflateBlock z start k P).eval (z (start+k))

def confluentTable (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ
  | 0, start => J 0 (z start)
  | k+1, start => if z (start+k+1) = z start then
      J (k+1) (z start) / ((k+1).factorial : ℝ)
    else (confluentTable z J k (start+1)-confluentTable z J k start) /
      (z (start+k+1)-z start)

def GroupedPrefix (z : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ start k, start+k < N → z (start+k) = z start →
    ∀ j ≤ k, z (start+j) = z start

theorem polynomialDeflateBlock_commute (z : ℕ → ℝ) (start k : ℕ) (x : ℝ) (P : Polynomial ℝ) :
    polynomialDeflateBlock z start k (polynomialDeflate x P) =
      polynomialDeflate x (polynomialDeflateBlock z start k P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [polynomialDeflateBlock, ih]
    exact polynomialDeflate_commute (z (start+k)) x _

theorem polynomialDeflateBlock_head (z : ℕ → ℝ) (start k : ℕ) (P : Polynomial ℝ) :
    polynomialDeflateBlock z start (k+1) P =
      polynomialDeflateBlock z (start+1) k (polynomialDeflate (z start) P) := by
  induction k with
  | zero => simp [polynomialDeflateBlock]
  | succ k ih =>
    change polynomialDeflate (z (start+(k+1))) (polynomialDeflateBlock z start (k+1) P) =
      polynomialDeflate (z ((start+1)+k))
        (polynomialDeflateBlock z (start+1) k (polynomialDeflate (z start) P))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (polynomialDeflate (z (start+(k+1)))) ih

theorem polynomialDD_rotate (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ) :
    polynomialDD z P k start = (polynomialDeflateBlock z (start+1) k P).eval (z start) := by
  cases k with
  | zero => simp [polynomialDD, polynomialDeflateBlock]
  | succ k =>
    rw [polynomialDD, polynomialDeflateBlock_head, polynomialDeflateBlock_commute,
      polynomialDeflate_eval_swap]
    simp only [polynomialDeflateBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem polynomialDD_secant (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ)
    (hne : z (start+k+1) ≠ z start) :
    polynomialDD z P (k+1) start =
      (polynomialDD z P k (start+1)-polynomialDD z P k start)/(z (start+k+1)-z start) := by
  rw [polynomialDD_rotate z P k start]
  rw [polynomialDD, polynomialDeflateBlock_head, polynomialDeflateBlock_commute]
  have h := polynomialDeflate_eval_relation (z start) (z (start+k+1))
    (polynomialDeflateBlock z (start+1) k P)
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  simp only [polynomialDD]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (show (polynomialDeflate (z start) (polynomialDeflateBlock z (start+1) k P)).eval
      (z (start+k+1)) * (z (start+k+1)-z start) =
      (polynomialDeflateBlock z (start+1) k P).eval (z (start+k+1)) -
      (polynomialDeflateBlock z (start+1) k P).eval (z start) by nlinarith [h])

theorem polynomialDeflateBlock_constant (z : ℕ → ℝ) (start k : ℕ) (x : ℝ)
    (P : Polynomial ℝ) (hz : ∀ j < k, z (start+j) = x) :
    polynomialDeflateBlock z start k P = (polynomialDeflate x)^[k] P := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [polynomialDeflateBlock, hz k (by omega), ih (fun j hj => hz j (by omega)),
      Function.iterate_succ_apply']

theorem confluentTable_polynomialDD (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) (k start : ℕ) (hbound : start+k < N) :
    confluentTable z (polynomialJets P) k start = polynomialDD z P k start := by
  induction k generalizing start with
  | zero => simp [confluentTable, polynomialDD, polynomialDeflateBlock, polynomialJets]
  | succ k ih =>
    rw [confluentTable]
    split_ifs with he
    · have hall : ∀ j ≤ k+1, z (start+j) = z start :=
        hz start (k+1) hbound (by simpa only [Nat.add_assoc] using he)
      rw [polynomialDD, polynomialDeflateBlock_constant z start (k+1) (z start) P
        (fun j hj => hall j (by omega)), hall (k+1) le_rfl]
      exact (polynomialDeflate_iterate_eval (z start) P (k+1)).symm
    · rw [ih (start+1) (by omega), ih start (by omega)]
      exact (polynomialDD_secant z P k start he).symm

theorem newtonBasis_succ (z : ℕ → ℝ) (N : ℕ) :
    newtonBasis z (N+1) = newtonBasis z N*(Polynomial.X-Polynomial.C (z N)) := by
  exact Finset.prod_range_succ _ N

theorem polynomial_newton_remainder (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ) :
    P = (∑ i ∈ Finset.range N, Polynomial.C (polynomialDD z P i 0)*newtonBasis z i) +
      newtonBasis z N*polynomialDeflateBlock z 0 N P := by
  induction N with
  | zero => simp [newtonBasis, polynomialDeflateBlock]
  | succ N ih =>
    rw [Finset.sum_range_succ, newtonBasis_succ, polynomialDeflateBlock]
    have h := polynomialDeflate_decomposition (z N) (polynomialDeflateBlock z 0 N P)
    simp only [polynomialDD, zero_add] at ih ⊢
    linear_combination ih+newtonBasis z N*h

theorem polynomialDeflate_degree_lt (x : ℝ) (P : Polynomial ℝ) (n : ℕ)
    (h : P.degree < (n+1 : ℕ)) : (polynomialDeflate x P).degree < n := by
  by_cases hP : P = 0
  · simp [hP, polynomialDeflate]
  have hn : P.natDegree < n+1 := by
    rw [Polynomial.degree_eq_natDegree hP] at h
    exact_mod_cast h
  have hle : P.degree ≤ (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hP]
    exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hn)
  exact (Polynomial.degree_divByMonic_lt P (Polynomial.X-Polynomial.C x) hP (by simp)).trans_le hle

theorem polynomialDeflateBlock_zero (z : ℕ → ℝ) (P : Polynomial ℝ) (N start : ℕ)
    (h : P.degree < N) : polynomialDeflateBlock z start N P = 0 := by
  induction N generalizing P start with
  | zero => exact Polynomial.degree_eq_bot.mp (WithBot.lt_coe_bot.mp h)
  | succ N ih =>
    rw [polynomialDeflateBlock_head]
    exact ih _ _ (polynomialDeflate_degree_lt (z start) P N h)

theorem newton_hermite_polynomial_newton (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) (hP : P.degree < N) :
    P = ∑ i ∈ Finset.range N, Polynomial.C (confluentTable z (polynomialJets P) i 0)*newtonBasis z i := by
  have h := polynomial_newton_remainder z P N
  rw [polynomialDeflateBlock_zero z P N 0 hP, mul_zero, add_zero] at h
  calc
    P = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [confluentTable_polynomialDD z P N hz i 0 (by simpa using Finset.mem_range.mp hi)]

#check newton_hermite_polynomial_newton
#print axioms newton_hermite_polynomial_newton
end Blueprint.Thomson.Finite
