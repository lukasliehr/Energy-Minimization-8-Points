import ThomsonCompact.CoeffMap.MomentProg
import ThomsonCompact.Packed.Comp
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor

/-!
# Soundness of the moment-polynomial mirror (F2b c)

`momentP_eq : momentP k i a = ev2 (mP k i) a` for all `k i a`, and for the D12 pivots the `√2` part vanishes
(`momRationalD12`, checked once), so `momentP k i a = evalQ (toQL (mP k i).r) a` (`momentP_D12`) — the form
evaluated by F1's `hornerQ` at the height TM.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open scoped BigOperators

/-- Real value of a coefficient list (Horner). -/
noncomputable def evq : List Rat → ℝ → ℝ
  | [], _ => 0
  | q :: L, a => (q : ℝ) + a * evq L a

/-- `r(a) + √2 s(a)`. -/
noncomputable def ev2 (p : Q2P) (a : ℝ) : ℝ := evq p.r a + Real.sqrt 2 * evq p.s a

theorem evq_qadd (a : ℝ) : ∀ p q : List Rat, evq (qadd p q) a = evq p a + evq q a
  | [], q => by simp [qadd, evq]
  | x :: p, [] => by simp [qadd, evq]
  | x :: p, y :: q => by
    simp only [qadd, evq, evq_qadd a p q]
    push_cast
    ring

theorem evq_qscale (x : Rat) (a : ℝ) : ∀ p : List Rat, evq (qscale x p) a = x * evq p a
  | [] => by simp [qscale, evq]
  | y :: p => by
    simp only [qscale, evq, evq_qscale x a p]
    push_cast
    ring

theorem evq_qmul (a : ℝ) : ∀ p q : List Rat, evq (qmul p q) a = evq p a * evq q a
  | [], q => by simp [qmul, evq]
  | x :: p, q => by
    simp only [qmul, evq_qadd, evq_qscale, evq, evq_qmul a p q]
    push_cast
    ring

theorem sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem ev2_add (p q : Q2P) (a : ℝ) : ev2 (q2add p q) a = ev2 p a + ev2 q a := by
  simp only [ev2, q2add, evq_qadd]
  ring

theorem ev2_mul (p q : Q2P) (a : ℝ) : ev2 (q2mul p q) a = ev2 p a * ev2 q a := by
  simp only [ev2, q2mul, evq_qadd, evq_qscale, evq_qmul]
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  linear_combination (-(evq p.s a * evq q.s a)) * h

theorem ev2_smul (x : Rat) (p : Q2P) (a : ℝ) : ev2 (q2smul x p) a = x * ev2 p a := by
  simp only [ev2, q2smul, evq_qscale]
  ring

theorem ev2_one (a : ℝ) : ev2 q2one a = 1 := by simp [ev2, q2one, evq]
theorem ev2_zero (a : ℝ) : ev2 q2zero a = 0 := by simp [ev2, q2zero, evq]
theorem ev2_X (a : ℝ) : ev2 q2X a = a := by simp [ev2, q2X, evq]

theorem ev2_pow (p : Q2P) (a : ℝ) : ∀ n, ev2 (q2pow p n) a = ev2 p a ^ n
  | 0 => by simp [q2pow, ev2_one]
  | n + 1 => by rw [q2pow, ev2_mul, ev2_pow p a n, pow_succ]

theorem chooseI_eq : ∀ n k, chooseI n k = Nat.choose n k
  | _, 0 => by simp [chooseI]
  | 0, _ + 1 => by simp [chooseI]
  | n + 1, k + 1 => by rw [chooseI, chooseI_eq n k, chooseI_eq n (k + 1), Nat.choose_succ_succ]

theorem sign_eq (j : ℕ) : ((if (j / 2) % 2 = 0 then 1 else -1 : Rat) : ℝ) = (-1 : ℝ) ^ (j / 2) := by
  rcases Nat.even_or_odd (j / 2) with h | h
  · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]; simp
  · rw [if_neg (by have := Nat.odd_iff.mp h; omega), h.neg_one_pow]; simp

theorem ev2_mRterm (k : ℕ) (c d : Q2P) (j : ℕ) (a : ℝ) :
    ev2 (mRterm k c d j) a =
      (k.choose j : ℝ) * ev2 c a ^ (k - j) * ev2 d a ^ j * (-1) ^ (j / 2) * a ^ ((k - j - k % 2) / 2) := by
  simp only [mRterm, ev2_mul, ev2_smul, ev2_pow, ev2_X]
  push_cast
  rw [sign_eq, chooseI_eq]
  ring

theorem ev2_mRsum (k : ℕ) (c d : Q2P) (a : ℝ) : ∀ L : List ℕ,
    ev2 (mRsum k c d L) a = (L.map fun j =>
      (k.choose j : ℝ) * ev2 c a ^ (k - j) * ev2 d a ^ j * (-1) ^ (j / 2) * a ^ ((k - j - k % 2) / 2)).sum
  | [] => by simp [mRsum, ev2_zero]
  | j :: L => by rw [mRsum, ev2_add, ev2_mRterm, ev2_mRsum k c d a L, List.map_cons, List.sum_cons]

theorem finset_filter_range_sum {M : Type*} [AddCommMonoid M] (p : ℕ → Prop) [DecidablePred p] (f : ℕ → M) :
    ∀ n, ∑ j ∈ (Finset.range n).filter p, f j = (((List.range n).filter (fun j => decide (p j))).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.filter_append, List.map_append,
      List.sum_append, ← finset_filter_range_sum p f n]
    by_cases hp : p n
    · rw [if_pos hp, Finset.sum_insert (by simp)]
      simp [hp, add_comm]
    · rw [if_neg hp]
      simp [hp]

theorem ev2_mR (k : ℕ) (c d : Q2P) (a : ℝ) : ev2 (mR k c d) a = momentR k (ev2 c a) (ev2 d a) a := by
  rw [mR, ev2_mRsum, momentR, finset_filter_range_sum (fun j => j % 2 = 0)]

theorem inv_sqrt2 : 1 / Real.sqrt 2 = Real.sqrt 2 * (1 / 2) := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem ev2_contacts (a : ℝ) :
    ev2 cA a = contacts a 0 ∧ ev2 cB a = contacts a 1 ∧ ev2 cC a = contacts a 2 ∧ ev2 cD a = contacts a 3 := by
  have h := inv_sqrt2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cA, ev2, q2X, evq, contacts]
  · simp [cB, ev2, evq, contacts]; ring
  · simp only [cC, ev2, evq, contacts]; simp; rw [div_eq_mul_one_div (1 - a), h]; push_cast; ring
  · simp only [cD, ev2, evq, contacts]; simp; rw [div_eq_mul_one_div (1 - a), h]; push_cast; ring

/-- **The mirror is exact.** -/
theorem momentP_eq (k i : ℕ) (a : ℝ) : momentP k i a = ev2 (mP k i) a := by
  obtain ⟨h0, h1, h2, h3⟩ := ev2_contacts a
  have hs := inv_sqrt2
  by_cases hk : k = 0
  · subst hk
    simp only [momentP, mP, if_true, ev2_add, ev2_smul, ev2_pow, ev2_one, h0, h1, h2, h3]
    push_cast
    ring
  · simp only [momentP, mP, hk, if_false, ev2_add, ev2_smul, ev2_pow, ev2_mul, ev2_one, ev2_X, ev2_mR,
      h0, h1, h2, h3]
    have e1 : ev2 ⟨[-1], [-1/2]⟩ a = -1 - 1 / Real.sqrt 2 := by
      simp only [ev2, evq]; rw [hs]; push_cast; ring
    have e2 : ev2 ⟨[0], [1/2]⟩ a = 1 / Real.sqrt 2 := by
      simp only [ev2, evq]; rw [hs]; push_cast; ring
    have e3 : ev2 ⟨[-1], [1/2]⟩ a = -1 + 1 / Real.sqrt 2 := by
      simp only [ev2, evq]; rw [hs]; push_cast; ring
    rw [e1, e2, e3]
    simp only [Nat.pow_eq]
    push_cast
    ring

theorem evq_allZero : ∀ (L : List Rat) (a : ℝ), qAllZero L = true → evq L a = 0
  | [], _, _ => rfl
  | x :: L, a, h => by
    simp only [qAllZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [evq, h.1, evq_allZero L a h.2]

theorem qval_toQ (q : Rat) : qval (decide (q < 0), q.num.natAbs, q.den) = (q : ℝ) := by
  unfold qval
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
    rw [Rat.cast_def]
  by_cases hn : q < 0
  · have hnum : q.num < 0 := Rat.num_neg.mpr hn
    simp only [hn, decide_true, if_true]
    rw [hq, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hnum)]
    ring
  · have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr (not_lt.mp hn)
    simp only [hn, decide_false, Bool.false_eq_true, if_false]
    rw [hq, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnum)]

theorem evalQ_toQL (a : ℝ) : ∀ L : List Rat, evalQ (toQL L) a = evq L a
  | [] => rfl
  | q :: L => by
    simp only [toQL, List.map_cons, evalQ, evq] at *
    rw [qval_toQ, ← evalQ_toQL a L]
    rfl

theorem momRationalD12_ok : momRationalD12 = true := by decide +kernel

/-- **D12 moment polynomials are rational**: the `hornerQ` form. -/
theorem momentP_D12 (k i : ℕ) (hk : k < 6) (hi : i < 7 - k) (a : ℝ) :
    momentP k i a = evalQ (toQL (mP k i).r) a := by
  have h := momRationalD12_ok
  simp only [momRationalD12, List.all_eq_true, List.mem_range] at h
  rw [momentP_eq, ev2, evq_allZero _ a (h k hk i hi), mul_zero, add_zero, evalQ_toQL]

#print axioms momentP_eq
#print axioms momentP_D12

end ThomsonCompact.CoeffMap
