import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_polynomial_newton
import AllS.Units.N_FI.N_newton_hermite.N_stage_invariant
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def sourceNewtonPolynomial (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N, Polynomial.C (confluentTable z J i 0)*newtonBasis z i

def sourceNewtonHorner (z : ℕ → ℝ) (c : ℕ → ℝ) : ℕ → ℕ → Polynomial ℝ
  | 0, _ => 0
  | N+1, start => Polynomial.C (c start)+(Polynomial.X-Polynomial.C (z start))*
      sourceNewtonHorner z c N (start+1)

theorem priorMultiplicity_of_window (z : ℕ → ℝ) (N start k : ℕ) (x : ℝ)
    (hbound : start+k < N) (hall : ∀ j ≤ k, z (start+j) = x) :
    k < priorMultiplicity z N x := by
  classical
  have hsub : Finset.Icc start (start+k) ⊆ (Finset.range N).filter (fun i => z i = x) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · have h := hall (i-start) (by omega)
      simpa only [Nat.add_sub_of_le hi'.1] using h
  have hcard := Finset.card_le_card hsub
  have hc : (Finset.Icc start (start+k)).card = k+1 := by simp only [Nat.card_Icc]; omega
  rw [hc] at hcard
  exact Nat.lt_of_succ_le hcard

theorem confluentTable_congr_jets (z : ℕ → ℝ) (J K : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N)
    (hJK : ∀ x k, k < priorMultiplicity z N x → J k x = K k x)
    (k start : ℕ) (hbound : start+k < N) :
    confluentTable z J k start = confluentTable z K k start := by
  induction k generalizing start with
  | zero =>
    apply hJK
    exact priorMultiplicity_of_window z N start 0 (z start) hbound
      (by
        intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        simp only [hj0, Nat.add_zero])
  | succ k ih =>
    simp only [confluentTable]
    split_ifs with he
    · rw [hJK (z start) (k+1)
        (priorMultiplicity_of_window z N start (k+1) (z start) hbound
          (hz start (k+1) hbound (by simpa only [Nat.add_assoc] using he)))]
    · rw [ih (start+1) (by omega), ih start (by omega)]

theorem sourceNewtonPolynomial_eq (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) : sourceNewtonPolynomial z J N = newtonHermite z J N := by
  symm
  have hstage := newton_hermite_stage_invariant z J N
  calc
    newtonHermite z J N = ∑ i ∈ Finset.range N,
        Polynomial.C (confluentTable z (polynomialJets (newtonHermite z J N)) i 0)*newtonBasis z i :=
      newton_hermite_polynomial_newton z _ N hz hstage.1
    _ = sourceNewtonPolynomial z J N := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [confluentTable_congr_jets z (polynomialJets (newtonHermite z J N)) J N hz
        hstage.2 i 0 (by simpa using Finset.mem_range.mp hi)]

@[simp] theorem newtonBasis_zero (z : ℕ → ℝ) : newtonBasis z 0 = 1 := by simp [newtonBasis]

theorem shifted_newtonBasis_succ (z : ℕ → ℝ) (start i : ℕ) :
    newtonBasis (fun k => z (start+k)) (i+1) =
      newtonBasis (fun k => z (start+1+k)) i*(Polynomial.X-Polynomial.C (z start)) := by
  simp only [newtonBasis, Finset.prod_range_succ', Nat.add_zero,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sourceNewtonHorner_eq_sum (z : ℕ → ℝ) (c : ℕ → ℝ) (N start : ℕ) :
    sourceNewtonHorner z c N start = ∑ i ∈ Finset.range N,
      Polynomial.C (c (start+i))*newtonBasis (fun k => z (start+k)) i := by
  induction N generalizing start with
  | zero => simp [sourceNewtonHorner]
  | succ N ih =>
    rw [sourceNewtonHorner, ih, Finset.sum_range_succ']
    simp_rw [shifted_newtonBasis_succ]
    simp only [newtonBasis_zero, Nat.add_zero, mul_one, ← mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Finset.sum_mul]
    ring

theorem sourceNewtonHorner_eq (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ) :
    sourceNewtonHorner z (fun i => confluentTable z J i 0) N 0 = sourceNewtonPolynomial z J N := by
  simpa only [sourceNewtonPolynomial, Nat.zero_add] using
    sourceNewtonHorner_eq_sum z (fun i => confluentTable z J i 0) N 0

theorem newton_hermite_confluent_bridge (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) :
    sourceNewtonPolynomial z J N = newtonHermite z J N ∧
    sourceNewtonHorner z (fun i => confluentTable z J i 0) N 0 = newtonHermite z J N :=
  ⟨sourceNewtonPolynomial_eq z J N hz,
    (sourceNewtonHorner_eq z J N).trans (sourceNewtonPolynomial_eq z J N hz)⟩

#check newton_hermite_confluent_bridge
#print axioms newton_hermite_confluent_bridge
end Blueprint.Thomson.Finite
