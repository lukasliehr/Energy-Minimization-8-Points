import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import ThomsonCompact.TailC.Stage

/-!
# TailC: values, digits and the specifications of the stage's loops (workstream TC1)

Values: `smv` (sign-magnitude), `ev` (entry in `ℤ√2`), `rv` (sign-split packed row in `ℤ√2`), `dig W X t` (digit `t`
of `X` in base `2^W`). Specs: `rv_addEnt`, `rv_packQ`, `walk_spec`, `rowsGo_spec`, `scatRow_spec`, `scatAll_spec`,
`decOut_spec` (all without bound hypotheses), `digit_sum` and the balanced decoding lemma `decode`.
-/

namespace ThomsonCompact.TailC
open Finset

/-! ## Nat primitives -/

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nsub (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nshl (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
theorem nshr (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
theorem mask_eq (w : ℕ) : mask w = 2 ^ w - 1 := by
  show Nat.shiftLeft 1 w - 1 = _
  rw [nshl, one_mul]
theorem land_mask (x w : ℕ) : Nat.land x (mask w) = x % 2 ^ w := by
  rw [mask_eq]; exact Nat.and_two_pow_sub_one_eq_mod x w
theorem fld_eq (x off w : ℕ) : fld x off w = x / 2 ^ off % 2 ^ w := by
  show Nat.land (Nat.shiftRight x off) (mask w) = _
  rw [land_mask, nshr]
theorem nbeq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]
theorem nblt (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
theorem nble (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]
theorem brec {α : Sort*} (f t : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) f t b = if b = true then t else f := by
  cases b <;> rfl

/-! ## Values -/

/-- Sign-magnitude value (`true` = negative). -/
def smv (x : Bool × Nat) : ℤ := if x.1 = true then -(x.2 : ℤ) else x.2

/-- Entry value `u + v √2`. -/
def ev (e : Ent) : ℤ√2 := ⟨smv e.2.1, smv e.2.2⟩

/-- Value of a sign-split row. -/
def rv (r : R4) : ℤ√2 := ⟨(r.1 : ℤ) - r.2.1, (r.2.2.1 : ℤ) - r.2.2.2⟩

/-- Digit `t` of `X` in base `2^W`. -/
def dig (W X t : ℕ) : ℕ := X / 2 ^ (W * t) % 2 ^ W

theorem abs_smv (x : Bool × Nat) : |smv x| = x.2 := by
  unfold smv; split_ifs <;> simp

theorem smv_mul2 (s : Bool) (m : ℕ) : smv (s, 2 * m) = 2 * smv (s, m) := by
  cases s <;> simp [smv]

theorem rv_zero : rv (0, 0, 0, 0) = 0 := by ext <;> simp [rv]

/-! ## `ℤ√2` sums and powers of two -/

def reH : (ℤ√2) →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := Zsqrtd.re_zero
  map_add' := Zsqrtd.re_add

def imH : (ℤ√2) →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := Zsqrtd.im_zero
  map_add' := Zsqrtd.im_add

theorem re_fsum {ι : Type*} (s : Finset ι) (f : ι → ℤ√2) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum reH f s
theorem im_fsum {ι : Type*} (s : Finset ι) (f : ι → ℤ√2) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum imH f s
theorem re_lsum (l : List (ℤ√2)) : l.sum.re = (l.map Zsqrtd.re).sum := map_list_sum reH l
theorem im_lsum (l : List (ℤ√2)) : l.sum.im = (l.map Zsqrtd.im).sum := map_list_sum imH l

theorem two_pow_eq (k : ℕ) : (2 : ℤ√2) ^ k = (((2 : ℤ) ^ k : ℤ) : ℤ√2) := by push_cast; rfl
theorem re_two_pow (k : ℕ) : ((2 : ℤ√2) ^ k).re = 2 ^ k := by rw [two_pow_eq, Zsqrtd.re_intCast]
theorem im_two_pow (k : ℕ) : ((2 : ℤ√2) ^ k).im = 0 := by rw [two_pow_eq, Zsqrtd.im_intCast]
theorem re_mul_two_pow (x : ℤ√2) (k : ℕ) : (x * 2 ^ k).re = x.re * 2 ^ k := by
  rw [Zsqrtd.re_mul, re_two_pow, im_two_pow]; ring
theorem im_mul_two_pow (x : ℤ√2) (k : ℕ) : (x * 2 ^ k).im = x.im * 2 ^ k := by
  rw [Zsqrtd.im_mul, re_two_pow, im_two_pow]; ring
theorem re_natCast_mul (c : ℕ) (x : ℤ√2) : ((c : ℤ√2) * x).re = c * x.re := by
  rw [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]; ring
theorem im_natCast_mul (c : ℕ) (x : ℤ√2) : ((c : ℤ√2) * x).im = c * x.im := by
  rw [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]; ring

/-! ## List and Finset sums -/

theorem lsum_fsum_comm {α β M : Type*} [AddCommMonoid M] (l : List α) (s : Finset β) (f : α → β → M) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

theorem lsum_mul_left {α R : Type*} [Semiring R] (l : List α) (c : R) (f : α → R) :
    c * (l.map f).sum = (l.map fun a => c * f a).sum := (List.sum_map_mul_left l f c).symm

theorem lsum_congr {α M : Type*} [AddCommMonoid M] (l : List α) (f g : α → M) (h : ∀ a ∈ l, f a = g a) :
    (l.map f).sum = (l.map g).sum := by rw [List.map_congr_left h]

theorem lsum_zero {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  rw [lsum_congr l f (fun _ => 0) h]; simp

theorem abs_lsum_le {α : Type*} (l : List α) (f : α → ℤ) : |(l.map f).sum| ≤ (l.map fun a => |f a|).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem lsum_le {α : Type*} (l : List α) (f g : α → ℤ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := List.sum_le_sum (by simpa using h)

/-- Regroup a list sum by an index `< n`. -/
theorem lsum_fiber {α M : Type*} [AddCommMonoid M] (l : List α) (φ : α → ℕ) (n : ℕ) (g : α → M)
    (h : ∀ a ∈ l, φ a < n) : (l.map g).sum = ∑ j ∈ range n, (l.map fun a => if φ a = j then g a else 0).sum := by
  rw [← lsum_fsum_comm]
  refine lsum_congr _ _ _ (fun a ha => ?_)
  rw [Finset.sum_ite_eq]; simp [h a ha]

/-! ## Digits -/

theorem digit_sum (B : ℕ) (hB : 0 < B) : ∀ (k n : ℕ) (d : ℕ → ℕ), (∀ j < n, d j < B) → k < n →
    (∑ j ∈ range n, d j * B ^ j) / B ^ k % B = d k
  | k, 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k, n + 1, d, hd, hk => by
    have hsplit : ∑ j ∈ range (n + 1), d j * B ^ j = d 0 + B * ∑ j ∈ range n, d (j + 1) * B ^ j := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm]; congr 1; refine Finset.sum_congr rfl (fun j _ => by ring)
    have h0 : d 0 < B := hd 0 (Nat.succ_pos n)
    cases k with
    | zero =>
      rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    | succ k =>
      rw [hsplit, pow_succ, mul_comm (B ^ k) B, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, zero_add]
      exact digit_sum B hB k n (fun j => d (j + 1)) (fun j hj => hd (j + 1) (by omega)) (by omega)

theorem biasN_eq (W n : ℕ) (hW : 1 ≤ W) : biasN W n = ∑ j ∈ range n, 2 ^ (W - 1) * 2 ^ (W * j) := by
  have hpos : 0 < 2 ^ W - 1 := by
    have : 2 ≤ 2 ^ W := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
    omega
  have hgeom : (∑ j ∈ range n, 2 ^ (W * j)) * (2 ^ W - 1) = 2 ^ (W * n) - 1 := by
    simp only [pow_mul]; exact geom_sum_mul_of_one_le Nat.one_le_two_pow n
  have hb : biasN W n = 2 ^ (W - 1) * (2 ^ (W * n) - 1) / (2 ^ W - 1) := by
    show Nat.div (Nat.mul (Nat.shiftLeft 1 (Nat.sub W 1)) (mask (Nat.mul W n))) (mask W) = _
    rw [nmul, nsub, nshl, one_mul, mask_eq, mask_eq, nmul]; rfl
  rw [hb, ← hgeom, ← mul_assoc, Nat.mul_div_cancel _ hpos, Finset.mul_sum]

/-- Balanced decoding: `P - N = Σ_{j<n} g_j 2^(W j)` with `|g_j| < 2^(W-1)` gives the digits of
`P + bias - N`. -/
theorem decode (W n : ℕ) (hW : 1 ≤ W) (g : ℕ → ℤ) (hg : ∀ j < n, |g j| < 2 ^ (W - 1)) (P N : ℕ)
    (hPN : (P : ℤ) - N = ∑ j ∈ range n, g j * 2 ^ (W * j)) :
    N ≤ P + biasN W n ∧ ∀ j < n, (dig W (P + biasN W n - N) j : ℤ) = g j + 2 ^ (W - 1) := by
  have hW2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hnn : ∀ j < n, 0 ≤ g j + 2 ^ (W - 1) := fun j hj => by
    have := abs_lt.1 (hg j hj); linarith
  have hlt : ∀ j < n, g j + 2 ^ (W - 1) < 2 ^ W := fun j hj => by
    have := abs_lt.1 (hg j hj); rw [hW2]; linarith
  set d : ℕ → ℕ := fun j => (g j + 2 ^ (W - 1)).toNat with hd
  have hdz : ∀ j < n, (d j : ℤ) = g j + 2 ^ (W - 1) := fun j hj => Int.toNat_of_nonneg (hnn j hj)
  have hdB : ∀ j < n, d j < 2 ^ W := fun j hj => by
    have := hlt j hj; rw [← hdz j hj] at this; exact_mod_cast this
  set X := ∑ j ∈ range n, d j * (2 ^ W) ^ j with hX
  have hXz : (X : ℤ) = (P : ℤ) - N + biasN W n := by
    rw [hX, biasN_eq W n hW, hPN]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hdz j (Finset.mem_range.1 hj), ← pow_mul]; ring
  have hle : N ≤ P + biasN W n := by
    have : (0 : ℤ) ≤ X := by positivity
    omega
  refine ⟨hle, fun j hj => ?_⟩
  have hXn : P + biasN W n - N = X := by omega
  rw [hXn, dig, pow_mul, hX, digit_sum (2 ^ W) (by positivity) j n d hdB hj, hdz j hj]

/-! ## Rows -/

theorem pv_smulP (s : Bool) (m P N : ℕ) :
    ((smulP s m P N).1 : ℤ) - (smulP s m P N).2 = smv (s, m) * ((P : ℤ) - N) := by
  cases s <;> simp [smulP, smv] <;> ring

theorem rv_addEnt (e : Ent) (Q r : R4) : rv (addEnt e Q r) = rv r + ev e * rv Q := by
  obtain ⟨i, ⟨su, mu⟩, ⟨sv, mv⟩⟩ := e
  obtain ⟨Q1, Q2, Q3, Q4⟩ := Q
  obtain ⟨r1, r2, r3, r4⟩ := r
  have a1 := pv_smulP su mu Q1 Q2
  have a2 := pv_smulP sv (2 * mv) Q3 Q4
  have b1 := pv_smulP su mu Q3 Q4
  have b2 := pv_smulP sv mv Q1 Q2
  rw [smv_mul2] at a2
  ext
  · simp only [rv, addEnt, nadd, nmul, Zsqrtd.re_add, Zsqrtd.re_mul, ev] at *
    push_cast
    linear_combination a1 + a2
  · simp only [rv, addEnt, nadd, nmul, Zsqrtd.im_add, Zsqrtd.im_mul, ev] at *
    push_cast
    linear_combination b1 + b2

theorem packQ_cons (W c : ℕ) (f : Ent) (fs : List Ent) : packQ W c (f :: fs) =
    (Bool.rec (motive := fun _ => Nat)
        (Nat.add (packQ W c fs).1 (Nat.shiftLeft (Nat.mul c f.2.1.2) (Nat.mul W f.1))) (packQ W c fs).1 f.2.1.1,
     Bool.rec (motive := fun _ => Nat) (packQ W c fs).2.1
        (Nat.add (packQ W c fs).2.1 (Nat.shiftLeft (Nat.mul c f.2.1.2) (Nat.mul W f.1))) f.2.1.1,
     Bool.rec (motive := fun _ => Nat)
        (Nat.add (packQ W c fs).2.2.1 (Nat.shiftLeft (Nat.mul c f.2.2.2) (Nat.mul W f.1))) (packQ W c fs).2.2.1
        f.2.2.1,
     Bool.rec (motive := fun _ => Nat) (packQ W c fs).2.2.2
        (Nat.add (packQ W c fs).2.2.2 (Nat.shiftLeft (Nat.mul c f.2.2.2) (Nat.mul W f.1))) f.2.2.1) := rfl

theorem rv_packQ (W c : ℕ) : ∀ q : List Ent,
    rv (packQ W c q) = (q.map fun f => (c : ℤ√2) * ev f * 2 ^ (W * f.1)).sum
  | [] => rv_zero
  | f :: fs => by
    rw [packQ_cons, List.map_cons, List.sum_cons, ← rv_packQ W c fs]
    obtain ⟨i, ⟨su, mu⟩, ⟨sv, mv⟩⟩ := f
    generalize packQ W c fs = r
    obtain ⟨r1, r2, r3, r4⟩ := r
    ext
    · rw [Zsqrtd.re_add, mul_assoc, re_natCast_mul, re_mul_two_pow]
      simp only [nadd, nmul, nshl]
      cases su <;> simp [rv, brec, ev, smv] <;> ring
    · rw [Zsqrtd.im_add, mul_assoc, im_natCast_mul, im_mul_two_pow]
      simp only [nadd, nmul, nshl]
      cases sv <;> simp [rv, brec, ev, smv] <;> ring

end ThomsonCompact.TailC
