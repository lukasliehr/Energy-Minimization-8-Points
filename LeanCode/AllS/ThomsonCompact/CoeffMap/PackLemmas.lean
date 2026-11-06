import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.Packed.Rep
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Generic lemmas for the packed W0 construction (F2c)

* `mkList_eq`, `listAt_mkList`: recursor-built tables and their lookups.
* `ZMod (2^K)` images of the kernel's `Nat` residues (`land` with `2^K - 1`, `2^K - y`).
* `colPack_cast`, `dPack_cast`: for any entry function `ent p l = (neg, mag)` (signed value `ival`), the column
  pass is `Σ_{l ≤ p < n} x(p,l) 2^(sw p)` and the Gram pass is `Σ_{p<n} 2^(sw p) Σ_{l ≤ min(p,q)} x(q,l) x(p,l)`
  modulo `2^K`, provided every placed magnitude fits (`mag · 2^(sw p) ≤ 2^K`).
* `horner_eq_sum`, `sum_range_mul`: coefficient lists as sums; reindexing `i = k + M p`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed
open scoped BigOperators

/-! ## Recursor-built lists -/

theorem mkList_aux {α : Type} (f : ℕ → α) : ∀ (n : ℕ) (acc : List α),
    (Nat.rec (motive := fun _ => List α → List α) (fun acc => acc) (fun t ih acc => ih (f t :: acc)) n) acc =
      (List.range n).map f ++ acc
  | 0, acc => by simp
  | n + 1, acc => by
    show (Nat.rec (motive := fun _ => List α → List α) (fun acc => acc) (fun t ih acc => ih (f t :: acc)) n)
      (f n :: acc) = _
    rw [mkList_aux f n, List.range_succ, List.map_append, List.append_assoc]
    rfl

theorem mkList_eq {α : Type} (f : ℕ → α) (n : ℕ) : mkList f n = (List.range n).map f := by
  unfold mkList
  rw [mkList_aux, List.append_nil]

theorem listAt_eq {α : Type} (d : α) : ∀ (L : List α) (i : ℕ), listAt d L i = L.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: L, i + 1 => by
    show listAt d L i = (a :: L).getD (i + 1) d
    rw [listAt_eq d L i, List.getD_cons_succ]

theorem listAt_mkList {α : Type} (d : α) (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    listAt d (mkList f n) i = f i := by
  rw [listAt_eq, mkList_eq, List.getD_eq_getElem?_getD]
  simp [hi]

theorem listAt_mkList_ge {α : Type} (d : α) (f : ℕ → α) {n i : ℕ} (hi : n ≤ i) :
    listAt d (mkList f n) i = d := by
  rw [listAt_eq, mkList_eq, List.getD_eq_getElem?_getD]
  simp [hi]

/-! ## Residues modulo `2^K` -/

theorem land_mask_eq (x K : ℕ) : Nat.land x (Nat.sub (2 ^ K) 1) = x % 2 ^ K :=
  Nat.and_two_pow_sub_one_eq_mod x K

theorem land_mask_lt (x K : ℕ) : Nat.land x (Nat.sub (2 ^ K) 1) < 2 ^ K := by
  rw [land_mask_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos K)

theorem natCast_land_mask (x K : ℕ) :
    ((Nat.land x (Nat.sub (2 ^ K) 1) : ℕ) : ZMod (2 ^ K)) = (x : ZMod (2 ^ K)) := by
  rw [land_mask_eq, ZMod.natCast_mod]

theorem natCast_sub_pow {K y : ℕ} (hy : y ≤ 2 ^ K) :
    ((Nat.sub (2 ^ K) y : ℕ) : ZMod (2 ^ K)) = -(y : ZMod (2 ^ K)) := by
  rw [show Nat.sub (2 ^ K) y = 2 ^ K - y from rfl, Nat.cast_sub hy, ZMod.natCast_self, zero_sub]

theorem natCast_mul_sub_pow {K m y : ℕ} (hy : y ≤ 2 ^ K) :
    ((Nat.mul m (Nat.sub (2 ^ K) y) : ℕ) : ZMod (2 ^ K)) = -((m : ZMod (2 ^ K)) * (y : ZMod (2 ^ K))) := by
  rw [show Nat.mul m (Nat.sub (2 ^ K) y) = m * Nat.sub (2 ^ K) y from rfl, Nat.cast_mul, natCast_sub_pow hy]
  ring

/-! ## Signed pairs -/

/-- Signed value of a `(neg, mag)` pair. -/
def ival (e : Bool × ℕ) : ℤ := if e.1 then -(e.2 : ℤ) else (e.2 : ℤ)

theorem ival_smSlot (z : ℕ) : ival (smSlot z) = sdec z := by
  unfold ival smSlot sdec
  by_cases h : Nat.land z 1 = 1
  · simp [h]
  · simp [h]

theorem abs_ival (e : Bool × ℕ) : |ival e| = (e.2 : ℤ) := by
  unfold ival
  split_ifs <;> simp

/-! ## The column pass -/

theorem colTerm_cast (K sw p : ℕ) (e : Bool × ℕ) (hy : e.2 * 2 ^ (sw * p) ≤ 2 ^ K) :
    ((colTerm (2 ^ K) sw p e : ℕ) : ZMod (2 ^ K)) = ((ival e : ℤ) : ZMod (2 ^ K)) * 2 ^ (sw * p) := by
  have hs : Nat.shiftLeft e.2 (Nat.mul sw p) = e.2 * 2 ^ (sw * p) := Nat.shiftLeft_eq _ _
  show ((cond e.1 (Nat.sub (2 ^ K) (Nat.shiftLeft e.2 (Nat.mul sw p))) (Nat.shiftLeft e.2 (Nat.mul sw p)) : ℕ) :
    ZMod (2 ^ K)) = _
  rw [hs]
  unfold ival
  cases h : e.1
  · simp
  · simp only [cond_true, if_true]
    rw [natCast_sub_pow hy]
    push_cast
    ring

theorem colAcc_cast (ent : ℕ → ℕ → Bool × ℕ) (sw K l n : ℕ)
    (hb : ∀ p, l ≤ p → p < n → (ent p l).2 * 2 ^ (sw * p) ≤ 2 ^ K) : ∀ k, k ≤ n →
    ((colAcc ent sw (2 ^ K) l k : ℕ) : ZMod (2 ^ K)) =
      ∑ p ∈ Finset.range k, if l ≤ p then ((ival (ent p l) : ℤ) : ZMod (2 ^ K)) * 2 ^ (sw * p) else 0
  | 0, _ => by simp [colAcc]
  | k + 1, hk => by
    rw [Finset.sum_range_succ, ← colAcc_cast ent sw K l n hb k (by omega)]
    show ((cond (Nat.ble l k) (Nat.add (colTerm (2 ^ K) sw k (ent k l)) (colAcc ent sw (2 ^ K) l k))
      (colAcc ent sw (2 ^ K) l k) : ℕ) : ZMod (2 ^ K)) = _
    by_cases h : l ≤ k
    · rw [show Nat.ble l k = true from Nat.ble_eq.mpr h, cond_true, if_pos h,
        show Nat.add (colTerm (2 ^ K) sw k (ent k l)) (colAcc ent sw (2 ^ K) l k) =
          colTerm (2 ^ K) sw k (ent k l) + colAcc ent sw (2 ^ K) l k from rfl, Nat.cast_add,
        colTerm_cast K sw k (ent k l) (hb k h (by omega))]
      ring
    · have hf : Nat.ble l k = false := by
        cases hb' : Nat.ble l k
        · rfl
        · exact absurd (Nat.ble_eq.mp hb') h
      rw [hf, cond_false, if_neg h, add_zero]

theorem colPack_lt (ent : ℕ → ℕ → Bool × ℕ) (sw K n l : ℕ) : colPack ent sw (2 ^ K) n l < 2 ^ K :=
  land_mask_lt _ _

theorem colPack_cast (ent : ℕ → ℕ → Bool × ℕ) (sw K n l : ℕ)
    (hb : ∀ p, l ≤ p → p < n → (ent p l).2 * 2 ^ (sw * p) ≤ 2 ^ K) :
    ((colPack ent sw (2 ^ K) n l : ℕ) : ZMod (2 ^ K)) =
      ∑ p ∈ Finset.range n, if l ≤ p then ((ival (ent p l) : ℤ) : ZMod (2 ^ K)) * 2 ^ (sw * p) else 0 := by
  unfold colPack
  rw [natCast_land_mask, colAcc_cast ent sw K l n hb n le_rfl]

/-! ## The Gram pass -/

theorem dAcc_cast (ent : ℕ → ℕ → Bool × ℕ) (sw K n q : ℕ) : ∀ k,
    ((dAcc ent sw (2 ^ K) n q k : ℕ) : ZMod (2 ^ K)) =
      ∑ l ∈ Finset.range k, ((ival (ent q l) : ℤ) : ZMod (2 ^ K)) * (colPack ent sw (2 ^ K) n l : ZMod (2 ^ K))
  | 0 => by simp [dAcc]
  | k + 1 => by
    rw [Finset.sum_range_succ, ← dAcc_cast ent sw K n q k]
    show ((Nat.add (cond (ent q k).1 (Nat.mul (ent q k).2 (colNeg ent sw (2 ^ K) n k))
      (Nat.mul (ent q k).2 (colPack ent sw (2 ^ K) n k))) (dAcc ent sw (2 ^ K) n q k) : ℕ) : ZMod (2 ^ K)) = _
    rw [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, Nat.cast_add, add_comm]
    congr 1
    unfold ival colNeg
    cases h : (ent q k).1
    · simp
    · simp only [cond_true, if_true]
      rw [natCast_mul_sub_pow (colPack_lt ent sw K n k).le]
      push_cast
      ring

theorem dPack_cast (ent : ℕ → ℕ → Bool × ℕ) (sw K n q : ℕ)
    (hb : ∀ p l, l ≤ p → p < n → (ent p l).2 * 2 ^ (sw * p) ≤ 2 ^ K) :
    ((dPack ent sw (2 ^ K) n q : ℕ) : ZMod (2 ^ K)) =
      ∑ p ∈ Finset.range n, (((∑ l ∈ Finset.range (q + 1),
        if l ≤ p then ival (ent q l) * ival (ent p l) else 0 : ℤ) : ZMod (2 ^ K)) * 2 ^ (sw * p)) := by
  unfold dPack
  rw [natCast_land_mask, show Nat.add q 1 = q + 1 from rfl, dAcc_cast]
  simp_rw [colPack_cast ent sw K n _ (fun p hl hp => hb p _ hl hp), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

/-! ## Coefficient lists as sums -/

theorem horner_eq_sum {R : Type*} [CommSemiring R] (t : R) : ∀ L : List R,
    horner t L = ∑ i ∈ Finset.range L.length, L.getD i 0 * t ^ i
  | [] => by simp
  | c :: cs => by
    rw [horner_cons, horner_eq_sum t cs, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem sum_range_mul {M' : Type*} [AddCommMonoid M'] (f : ℕ → M') (M : ℕ) : ∀ n,
    ∑ i ∈ Finset.range (M * n), f i = ∑ p ∈ Finset.range n, ∑ k ∈ Finset.range M, f (k + M * p)
  | 0 => by simp
  | n + 1 => by
    rw [show M * (n + 1) = M * n + M by ring, Finset.sum_range_add, sum_range_mul f M n, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm]

theorem sum_range_extend {M' : Type*} [AddCommMonoid M'] (g : ℕ → M') {m n : ℕ} (h : m ≤ n) :
    ∑ l ∈ Finset.range m, g l = ∑ l ∈ Finset.range n, if l < m then g l else 0 := by
  rw [← Finset.sum_filter, show (Finset.range n).filter (· < m) = Finset.range m by
    ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega]

end ThomsonCompact.CoeffMap
