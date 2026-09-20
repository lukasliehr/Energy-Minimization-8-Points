import Coulomb8.Witness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
open scoped BigOperators

theorem sum_getD_natAbs (xs : List ℤ) :
    (∑ i : Fin xs.length, (xs.getD i.val 0).natAbs)=(xs.map Int.natAbs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Fin.sum_univ_succ,ih]

theorem sum_getD_natAbs_of_length (xs : List ℤ) (n : ℕ) (hn : xs.length=n) :
    (∑ i : Fin n, (xs.getD i.val 0).natAbs)=(xs.map Int.natAbs).sum := by
  subst n
  exact sum_getD_natAbs xs

theorem scaled_integer_row_bound {ι : Type*} [Fintype ι] (cs : ι → ℤ)
    (h : (∑ j, (cs j).natAbs) ≤ 2^56) :
    ∑ j, |(cs j : ℝ)/(2^40 : ℝ)| ≤ (65536 : ℝ) := by
  have hz : (∑ j, |cs j|) ≤ (2^56 : ℤ) := by
    have hh : ((∑ j, (cs j).natAbs : ℕ) : ℤ) ≤ ((2^56 : ℕ) : ℤ) := Nat.cast_le.mpr h
    simpa only [Nat.cast_sum,Int.natCast_natAbs,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hr : ∑ j, |(cs j : ℝ)| ≤ (2^56 : ℝ) := by exact_mod_cast hz
  simp only [abs_div,abs_of_pos (show (0 : ℝ) < 2^40 by norm_num)]
  rw [←Finset.sum_div]
  apply (div_le_iff₀ (show (0 : ℝ) < 2^40 by norm_num)).mpr
  exact hr.trans_eq (by norm_num)

theorem preconditioner_row_norm (i : Fin 99) :
    ∑ j, |Witness.preconditioner i j| ≤ (65536 : ℝ) := by
  apply scaled_integer_row_bound (Witness.inverseNumerators i)
  exact (sum_getD_natAbs_of_length (Witness.inverseRows i) 99
    (Witness.inverseRows_length i)).le.trans (Witness.inverseRows_bound i)

end Coulomb8

#print axioms Coulomb8.preconditioner_row_norm
