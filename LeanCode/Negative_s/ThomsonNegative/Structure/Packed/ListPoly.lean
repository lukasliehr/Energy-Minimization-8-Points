import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Polynomials as coefficient lists (generic semiring)

`addL`, `scaleL`, `convL` follow `LeanSupport/Pilot/BalancedProof.lean` (`add`, `scale`, `conv`), generalized
from `ℤ` to any semiring; `horner t L = Σ Lᵢ tⁱ`. The Kronecker identity `horner_convL` covers both the packed
integer encoding (`t = 2^W`) and real evaluation (`t ∈ [-1,1]`). `Dom a α` is coefficientwise domination
`|aₖ| ≤ αₖ`.
-/

namespace ThomsonNegative.Structure.Packed

universe u
variable {R : Type u}

def addL [Add R] : List R → List R → List R
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

def scaleL [Mul R] (a : R) : List R → List R
  | [] => []
  | x :: xs => (a * x) :: scaleL a xs

def convL [Semiring R] : List R → List R → List R
  | [], _ => []
  | x :: xs, ys => addL (scaleL x ys) (0 :: convL xs ys)

/-- `horner t L = Σ Lᵢ tⁱ` -/
def horner [Semiring R] (t : R) : List R → R
  | [] => 0
  | c :: cs => c + t * horner t cs

section Semiring
variable [Semiring R]

@[simp] theorem horner_nil (t : R) : horner t ([] : List R) = 0 := rfl
@[simp] theorem horner_cons (t c : R) (cs : List R) : horner t (c :: cs) = c + t * horner t cs := rfl

theorem length_addL : ∀ a b : List R, (addL a b).length = max a.length b.length
  | [], b => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp [addL, length_addL xs ys, Nat.succ_max_succ]

theorem length_scaleL (x : R) : ∀ a : List R, (scaleL x a).length = a.length
  | [] => rfl
  | y :: ys => by simp [scaleL, length_scaleL x ys]

theorem length_convL (b : List R) (hb : b ≠ []) :
    ∀ a : List R, a ≠ [] → (convL a b).length = a.length + b.length - 1
  | [], h => absurd rfl h
  | [x], _ => by
    have := List.length_pos_of_ne_nil hb
    simp only [convL, length_addL, length_scaleL, List.length_cons, List.length_nil]
    omega
  | x :: y :: ys, _ => by
    have ih := length_convL b hb (y :: ys) (by simp)
    have := List.length_pos_of_ne_nil hb
    rw [convL, length_addL, length_scaleL, List.length_cons, ih]
    simp only [List.length_cons]
    omega

theorem getD_addL : ∀ (a b : List R) (k : ℕ), (addL a b).getD k 0 = a.getD k 0 + b.getD k 0
  | [], b, k => by simp [addL]
  | x :: xs, [], k => by simp [addL]
  | x :: xs, y :: ys, 0 => by simp [addL]
  | x :: xs, y :: ys, k + 1 => by simp only [addL, List.getD_cons_succ]; exact getD_addL xs ys k

theorem getD_scaleL (x : R) : ∀ (a : List R) (k : ℕ), (scaleL x a).getD k 0 = x * a.getD k 0
  | [], k => by simp [scaleL]
  | y :: ys, 0 => by simp [scaleL]
  | y :: ys, k + 1 => by simp only [scaleL, List.getD_cons_succ]; exact getD_scaleL x ys k

end Semiring

section CommSemiring
variable [CommSemiring R]

theorem horner_addL (t : R) : ∀ a b : List R, horner t (addL a b) = horner t a + horner t b
  | [], b => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp only [addL, horner_cons, horner_addL t xs ys]; ring

theorem horner_scaleL (t x : R) : ∀ a : List R, horner t (scaleL x a) = x * horner t a
  | [] => by simp [scaleL]
  | y :: ys => by simp only [scaleL, horner_cons, horner_scaleL t x ys]; ring

/-- Kronecker identity (generalizes `BalancedProof.encode_conv`). -/
theorem horner_convL (t : R) : ∀ a b : List R, horner t (convL a b) = horner t a * horner t b
  | [], b => by simp [convL]
  | x :: xs, b => by
    simp only [convL, horner_addL, horner_scaleL, horner_cons, horner_convL t xs b]; ring

theorem horner_one (a : List R) : horner 1 a = a.sum := by
  induction a with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem sum_convL (a b : List R) : (convL a b).sum = a.sum * b.sum := by
  rw [← horner_one, horner_convL, horner_one, horner_one]

theorem horner_take_drop (t : R) : ∀ (n : ℕ) (a : List R),
    horner t a = horner t (a.take n) + t ^ n * horner t (a.drop n)
  | 0, a => by simp
  | n + 1, [] => by simp
  | n + 1, c :: cs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, horner_cons, horner_take_drop t n cs]; ring

end CommSemiring

section Map
variable {S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

theorem map_addL : ∀ a b : List R, (addL a b).map f = addL (a.map f) (b.map f)
  | [], b => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp [addL, map_addL xs ys]

theorem map_scaleL (x : R) : ∀ a : List R, (scaleL x a).map f = scaleL (f x) (a.map f)
  | [] => by simp [scaleL]
  | y :: ys => by simp [scaleL, map_scaleL x ys]

theorem map_convL : ∀ a b : List R, (convL a b).map f = convL (a.map f) (b.map f)
  | [], b => by simp [convL]
  | x :: xs, b => by simp [convL, map_addL, map_scaleL, map_convL xs b]

theorem map_horner (t : R) : ∀ a : List R, f (horner t a) = horner (f t) (a.map f)
  | [] => by simp
  | c :: cs => by simp [map_horner t cs]

end Map

/-! ## Coefficientwise domination -/

/-- `|aₖ| ≤ αₖ` for every index `k` (missing entries count as `0`). -/
def Dom (a : List ℤ) (α : List ℕ) : Prop := ∀ k, |a.getD k 0| ≤ ((α.getD k 0 : ℕ) : ℤ)

theorem Dom.addL {a b : List ℤ} {α β : List ℕ} (ha : Dom a α) (hb : Dom b β) :
    Dom (addL a b) (addL α β) := by
  intro k
  rw [getD_addL, getD_addL]
  push_cast
  exact (abs_add_le _ _).trans (add_le_add (ha k) (hb k))

theorem Dom.scaleL {x : ℤ} {y : ℕ} (hxy : |x| ≤ (y : ℤ)) {a : List ℤ} {α : List ℕ} (ha : Dom a α) :
    Dom (scaleL x a) (scaleL y α) := by
  intro k
  rw [getD_scaleL, getD_scaleL]
  push_cast
  rw [abs_mul]
  exact mul_le_mul hxy (ha k) (abs_nonneg _) (by positivity)

theorem Dom.cons0 {a : List ℤ} {α : List ℕ} (ha : Dom a α) : Dom (0 :: a) (0 :: α) := by
  intro k
  cases k with
  | zero => simp
  | succ k => simpa using ha k

theorem Dom.tail {x : ℤ} {y : ℕ} {a : List ℤ} {α : List ℕ} (h : Dom (x :: a) (y :: α)) :
    |x| ≤ (y : ℤ) ∧ Dom a α :=
  ⟨by simpa using h 0, fun k => by simpa using h (k + 1)⟩

theorem Dom.convL {b : List ℤ} {β : List ℕ} (hb : Dom b β) :
    ∀ (a : List ℤ) (α : List ℕ), a.length = α.length → Dom a α → Dom (convL a b) (convL α β)
  | [], [], _, _ => by intro k; simp [ThomsonNegative.Structure.Packed.convL]
  | x :: xs, y :: ys, hl, ha => by
    obtain ⟨hx, hxs⟩ := ha.tail
    have ih := Dom.convL hb xs ys (by simpa using hl) hxs
    simp only [ThomsonNegative.Structure.Packed.convL]
    exact (hb.scaleL hx).addL ih.cons0
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem Dom.drop {a : List ℤ} {α : List ℕ} (h : Dom a α) (n : ℕ) : Dom (a.drop n) (α.drop n) := by
  intro k
  simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using h (n + k)

theorem Dom.take {a : List ℤ} {α : List ℕ} (h : Dom a α) (n : ℕ) : Dom (a.take n) (α.take n) := by
  intro k
  by_cases hk : k < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_take, hk] using h k
  · simp [List.getD_eq_getElem?_getD, hk]

/-- Sum of magnitudes is dominated. -/
theorem Dom.sum_abs_le : ∀ (a : List ℤ) (α : List ℕ), Dom a α → ((a.map abs).sum : ℤ) ≤ ((α.sum : ℕ) : ℤ)
  | [], α, _ => by simp
  | x :: xs, [], h => by
    have h0 : |x| ≤ 0 := by simpa using h 0
    have hr : Dom xs [] := fun k => by simpa using h (k + 1)
    have := Dom.sum_abs_le xs [] hr
    simp only [List.map_cons, List.sum_cons, List.sum_nil, Nat.cast_zero] at this ⊢
    linarith
  | x :: xs, y :: ys, h => by
    obtain ⟨hx, hr⟩ := h.tail
    have := Dom.sum_abs_le xs ys hr
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    linarith

/-- Real evaluation of an integer coefficient list. -/
noncomputable def evalZ (cs : List ℤ) (t : ℝ) : ℝ := horner t (cs.map (Int.cast : ℤ → ℝ))

theorem evalZ_convL (a b : List ℤ) (t : ℝ) : evalZ (convL a b) t = evalZ a t * evalZ b t := by
  have h := map_convL (Int.castRingHom ℝ) a b
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, h, horner_convL]

theorem abs_horner_le (t : ℝ) (ht : |t| ≤ 1) : ∀ a : List ℝ, |horner t a| ≤ (a.map abs).sum
  | [] => by simp
  | c :: cs => by
    have ih := abs_horner_le t ht cs
    simp only [horner_cons, List.map_cons, List.sum_cons]
    calc |c + t * horner t cs| ≤ |c| + |t| * |horner t cs| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |c| + 1 * (cs.map abs).sum := by gcongr
      _ = |c| + (cs.map abs).sum := by ring

theorem abs_evalZ_le {cs : List ℤ} {α : List ℕ} (h : Dom cs α) (t : ℝ) (ht : |t| ≤ 1) :
    |evalZ cs t| ≤ (α.sum : ℝ) := by
  have h1 := abs_horner_le t ht (cs.map (Int.cast : ℤ → ℝ))
  have h2 := Dom.sum_abs_le cs α h
  have h3 : ∀ l : List ℤ, ((l.map (Int.cast : ℤ → ℝ)).map abs).sum = (((l.map abs).sum : ℤ) : ℝ) := by
    intro l
    induction l with
    | nil => simp
    | cons z zs ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_abs]
      rw [ih]
  rw [evalZ]
  refine h1.trans ?_
  rw [h3 cs]
  exact_mod_cast h2

end ThomsonNegative.Structure.Packed
