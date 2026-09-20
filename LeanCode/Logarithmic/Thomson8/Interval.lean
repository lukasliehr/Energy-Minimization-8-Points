import Thomson8.Algebra
import Mathlib.Data.Rat.Floor

namespace Thomson8

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace Box

def Contains (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def exact (q : ℚ) : Box := ⟨q,q⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
def sub (a b : Box) : Box := add a (neg b)
def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

def scale : ℚ := 2^128
def down (q : ℚ) : ℚ := (⌊q*scale⌋ : ℚ)/scale
def up (q : ℚ) : ℚ := (⌈q*scale⌉ : ℚ)/scale
def round (b : Box) : Box := ⟨down b.lo, up b.hi⟩
def times (a b : Box) : Box := round (mul a b)
def rational (q : ℚ) : Box := round (exact q)

theorem exact_contains (q : ℚ) : (exact q).Contains (q : ℝ) := ⟨le_rfl,le_rfl⟩

theorem contains_add {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (add a b).Contains (x+y) := by
  dsimp [Contains, add] at *
  push_cast
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem contains_neg {a : Box} {x : ℝ} (hx : a.Contains x) : (neg a).Contains (-x) := by
  dsimp [Contains, neg] at *
  push_cast
  constructor <;> linarith [hx.1,hx.2]

theorem contains_sub {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (sub a b).Contains (x-y) := by
  simpa [sub_eq_add_neg, sub] using contains_add hx (contains_neg hy)

private theorem lower_mul {l x u a L : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : L ≤ l*a) (hu : L ≤ u*a) : L ≤ x*a := by
  by_cases ha : 0 ≤ a
  · exact hl.trans (mul_le_mul_of_nonneg_right hx.1 ha)
  · exact hu.trans (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge ha))

private theorem upper_mul {l x u a U : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : l*a ≤ U) (hu : u*a ≤ U) : x*a ≤ U := by
  by_cases ha : 0 ≤ a
  · exact (mul_le_mul_of_nonneg_right hx.2 ha).trans hu
  · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge ha)).trans hl

theorem contains_mul {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mul a b).Contains (x*y) := by
  dsimp [Contains, mul] at *
  push_cast
  constructor
  · apply lower_mul hx
    · rw [mul_comm (a.lo : ℝ) y]
      apply lower_mul hy
      · simpa only [mul_comm] using (min_le_left _ _).trans (min_le_left _ _)
      · simpa only [mul_comm] using (min_le_left _ _).trans (min_le_right _ _)
    · rw [mul_comm (a.hi : ℝ) y]
      apply lower_mul hy
      · simpa only [mul_comm] using (min_le_right _ _).trans (min_le_left _ _)
      · simpa only [mul_comm] using (min_le_right _ _).trans (min_le_right _ _)
  · apply upper_mul hx
    · rw [mul_comm (a.lo : ℝ) y]
      apply upper_mul hy
      · simpa only [mul_comm] using (le_max_left _ _).trans (le_max_left _ _)
      · simpa only [mul_comm] using (le_max_right _ _).trans (le_max_left _ _)
    · rw [mul_comm (a.hi : ℝ) y]
      apply upper_mul hy
      · simpa only [mul_comm] using (le_max_left _ _).trans (le_max_right _ _)
      · simpa only [mul_comm] using (le_max_right _ _).trans (le_max_right _ _)

theorem scale_pos : (0 : ℚ) < scale := by norm_num [scale]
theorem down_le (q : ℚ) : down q ≤ q := by
  rw [down, div_le_iff₀ scale_pos]
  exact Int.floor_le _
theorem le_up (q : ℚ) : q ≤ up q := by
  rw [up, le_div_iff₀ scale_pos]
  exact Int.le_ceil _

theorem contains_round {b : Box} {x : ℝ} (hx : b.Contains x) : (round b).Contains x := by
  constructor
  · exact (Rat.cast_le.mpr (down_le b.lo)).trans hx.1
  · exact hx.2.trans (Rat.cast_le.mpr (le_up b.hi))

theorem contains_times {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (times a b).Contains (x*y) := contains_round (contains_mul hx hy)

theorem contains_rational (q : ℚ) : (rational q).Contains (q : ℝ) :=
  contains_round (exact_contains q)

def inverse (b : Box) : Box := round ⟨b.hi⁻¹,b.lo⁻¹⟩
def divide (a b : Box) : Box := times a (inverse b)

theorem contains_inverse {b : Box} {x : ℝ} (hb : 0 < b.lo) (hx : b.Contains x) :
    (inverse b).Contains x⁻¹ := by
  apply contains_round
  have hl : (0 : ℝ) < b.lo := Rat.cast_pos.mpr hb
  have hxp : 0 < x := hl.trans_le hx.1
  constructor
  · dsimp
    rw [Rat.cast_inv]
    exact inv_anti₀ hxp hx.2
  · dsimp
    rw [Rat.cast_inv]
    exact inv_anti₀ hl hx.1

theorem contains_divide {a b : Box} {x y : ℝ}
    (hb : 0 < b.lo) (hx : a.Contains x) (hy : b.Contains y) :
    (divide a b).Contains (x/y) := by
  simpa only [divide, div_eq_mul_inv] using contains_times hx (contains_inverse hb hy)

def pow (b : Box) : ℕ → Box
  | 0 => exact 1
  | n+1 => times (pow b n) b

theorem contains_pow {b : Box} {x : ℝ} (hx : b.Contains x) (n : ℕ) :
    (pow b n).Contains (x^n) := by
  induction n with
  | zero => simpa [pow] using exact_contains 1
  | succ n ih => simpa [pow, pow_succ] using contains_times ih hx

def sum : List Box → Box
  | [] => exact 0
  | b::bs => add b (sum bs)

theorem contains_sum {bs : List Box} {xs : List ℝ}
    (h : List.Forall₂ Contains bs xs) : (sum bs).Contains xs.sum := by
  induction h with
  | nil => simpa [sum] using exact_contains 0
  | cons hx _ ih => simpa [sum] using contains_add hx ih

def field (root2 root58 : Box) (x : K) : Box :=
  add (add (add (rational x.c0) (times (rational x.c1) root2))
    (times (rational x.c2) root58))
    (times (times (rational x.c3) root2) root58)

theorem contains_field {r s : Box} (hr : r.Contains (Real.sqrt 2))
    (hs : s.Contains (Real.sqrt 58)) (x : K) : (field r s x).Contains x.eval := by
  unfold field K.eval K.evalAt
  exact contains_add
    (contains_add (contains_add (contains_rational _) (contains_times (contains_rational _) hr))
      (contains_times (contains_rational _) hs))
    (contains_times (contains_times (contains_rational _) hr) hs)

end Box
end Thomson8
