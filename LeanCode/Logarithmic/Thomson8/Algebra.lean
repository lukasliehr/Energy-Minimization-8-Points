import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Exact arithmetic used by the certificate, with its real interpretation.
The representation need not be injective: coordinate equality suffices.
-/
namespace Thomson8

structure K where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  deriving DecidableEq, Repr

namespace K

def ofRat (q : ℚ) : K := ⟨q, 0, 0, 0⟩
def zero : K := ofRat 0
def one : K := ofRat 1
def add (x y : K) : K := ⟨x.c0+y.c0, x.c1+y.c1, x.c2+y.c2, x.c3+y.c3⟩
def neg (x : K) : K := ⟨-x.c0, -x.c1, -x.c2, -x.c3⟩
def scale (q : ℚ) (x : K) : K := ⟨q*x.c0,q*x.c1,q*x.c2,q*x.c3⟩
def mul (x y : K) : K :=
  ⟨x.c0*y.c0+2*x.c1*y.c1+58*x.c2*y.c2+116*x.c3*y.c3,
   x.c0*y.c1+x.c1*y.c0+58*x.c2*y.c3+58*x.c3*y.c2,
   x.c0*y.c2+x.c2*y.c0+2*x.c1*y.c3+2*x.c3*y.c1,
   x.c0*y.c3+x.c3*y.c0+x.c1*y.c2+x.c2*y.c1⟩
def pow (x : K) : ℕ → K
  | 0 => one
  | n+1 => mul (pow x n) x

def evalAt (r s : ℝ) (x : K) : ℝ :=
  (x.c0 : ℝ) + (x.c1 : ℝ)*r + (x.c2 : ℝ)*s + (x.c3 : ℝ)*r*s

noncomputable def eval (x : K) : ℝ := evalAt (Real.sqrt 2) (Real.sqrt 58) x

@[simp] theorem evalAt_ofRat (r s : ℝ) (q : ℚ) :
    evalAt r s (ofRat q) = (q : ℝ) := by simp [evalAt, ofRat]

@[simp] theorem evalAt_add (r s : ℝ) (x y : K) :
    evalAt r s (add x y) = evalAt r s x + evalAt r s y := by
  simp only [evalAt, add, Rat.cast_add]
  ring

@[simp] theorem evalAt_neg (r s : ℝ) (x : K) :
    evalAt r s (neg x) = -evalAt r s x := by
  simp only [evalAt, neg, Rat.cast_neg]
  ring

@[simp] theorem evalAt_scale (r s : ℝ) (q : ℚ) (x : K) :
    evalAt r s (scale q x) = (q : ℝ)*evalAt r s x := by
  simp only [evalAt, scale, Rat.cast_mul]
  ring

theorem evalAt_mul (r s : ℝ) (hr : r^2=2) (hs : s^2=58) (x y : K) :
    evalAt r s (mul x y) = evalAt r s x * evalAt r s y := by
  simp only [evalAt, mul, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  ring_nf
  simp only [hr, hs]
  ring

@[simp] theorem eval_ofRat (q : ℚ) : eval (ofRat q) = (q : ℝ) :=
  evalAt_ofRat _ _ _
@[simp] theorem eval_zero : eval zero = 0 := by simp [zero]
@[simp] theorem eval_one : eval one = 1 := by simp [one]
@[simp] theorem eval_add (x y : K) : eval (add x y) = eval x + eval y :=
  evalAt_add _ _ _ _
@[simp] theorem eval_neg (x : K) : eval (neg x) = -eval x := evalAt_neg _ _ _
@[simp] theorem eval_scale (q : ℚ) (x : K) : eval (scale q x) = (q : ℝ)*eval x :=
  evalAt_scale _ _ _ _
@[simp] theorem eval_mul (x y : K) : eval (mul x y) = eval x * eval y :=
  evalAt_mul _ _ (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num)) _ _
@[simp] theorem eval_pow (x : K) (n : ℕ) : eval (pow x n) = eval x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

def sum : List K → K
  | [] => zero
  | x :: xs => add x (sum xs)

@[simp] theorem eval_sum (xs : List K) : eval (sum xs) = (xs.map eval).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih => simp [sum, ih]

end K
end Thomson8
