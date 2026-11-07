import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Blueprint.CAP.BoundaryDirect

abbrev Q2 := ℚ × ℚ
abbrev Word := List (Fin 13)
abbrev Poly := List (Word × Q2)

def qadd (a b : Q2) : Q2 := (a.1 + b.1, a.2 + b.2)
def qneg (a : Q2) : Q2 := (-a.1, -a.2)
def qmul (a b : Q2) : Q2 := (a.1*b.1+2*a.2*b.2, a.1*b.2+a.2*b.1)
noncomputable def qeval (a : Q2) : ℝ := a.1 + (a.2 : ℝ) * Real.sqrt 2
noncomputable def wordEval (w : Word) (y : Fin 13 → ℝ) : ℝ := (w.map y).prod
noncomputable def eval (p : Poly) (y : Fin 13 → ℝ) : ℝ :=
  (p.map fun t => qeval t.2 * wordEval t.1 y).sum

def wordLT : Word → Word → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.val = b.val then wordLT as bs else decide (a.val < b.val)

def wordInsert (i : Fin 13) : Word → Word
  | [] => [i]
  | j :: w => if i.val ≤ j.val then i :: j :: w else j :: wordInsert i w
def wordSort (w : Word) : Word := w.foldr wordInsert []

def insert (t : Word × Q2) : Poly → Poly
  | [] => [t]
  | s :: p => if t.1 = s.1 then (s.1, qadd t.2 s.2) :: p
      else if wordLT t.1 s.1 then t :: s :: p
      else s :: insert t p

def collect (p : Poly) : Poly := p.foldr insert []
def normalize (p : Poly) : Poly := (collect p).filter (fun t => t.2 != (0,0))
def neg (p : Poly) : Poly := p.map (fun t => (t.1, qneg t.2))
def add (p q : Poly) : Poly := normalize (p ++ q)
def mul (p q : Poly) : Poly := normalize (p.flatMap fun t => q.map fun s =>
  (wordSort (t.1 ++ s.1), qmul t.2 s.2))
def scale (c : Q2) (p : Poly) : Poly := p.map fun t => (t.1, qmul c t.2)
def weightedSquare (w : ℚ) (p : Poly) : Poly := scale (w,0) (mul p p)
def sum (ps : List Poly) : Poly := ps.foldr add []

theorem qeval_add (a b : Q2) : qeval (qadd a b) = qeval a + qeval b := by
  simp [qeval, qadd]; ring

theorem qeval_neg (a : Q2) : qeval (qneg a) = -qeval a := by
  simp [qeval, qneg]; ring

theorem qeval_mul (a b : Q2) : qeval (qmul a b) = qeval a * qeval b := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [qeval, qmul]
  ring_nf
  rw [hs]

theorem eval_insert (t : Word × Q2) (p : Poly) (y : Fin 13 → ℝ) :
    eval (insert t p) y = qeval t.2 * wordEval t.1 y + eval p y := by
  induction p with
  | nil => simp [insert, eval]
  | cons s p ih =>
    simp only [insert]
    split_ifs with h hlt
    · simp only [eval, List.map_cons, List.sum_cons, qeval_add]
      rw [h]
      ring
    · simp [eval]
    · change qeval s.2 * wordEval s.1 y + eval (insert t p) y = _
      rw [ih]
      simp only [eval, List.map_cons, List.sum_cons]
      ring

theorem eval_collect (p : Poly) (y : Fin 13 → ℝ) : eval (collect p) y = eval p y := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change eval (insert t (collect p)) y = _
    rw [eval_insert, ih]
    rfl

theorem eval_filter_zero (p : Poly) (y : Fin 13 → ℝ) :
    eval (p.filter (fun t => t.2 != (0,0))) y = eval p y := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases ht : t.2 = (0,0)
    · simp [ht, eval, qeval] at *
      exact ih
    · simpa [List.filter_cons, ht, eval] using congrArg (qeval t.2 * wordEval t.1 y + ·) ih

theorem eval_normalize (p : Poly) (y : Fin 13 → ℝ) : eval (normalize p) y = eval p y := by
  rw [normalize, eval_filter_zero, eval_collect]

theorem eval_append (p q : Poly) (y : Fin 13 → ℝ) : eval (p ++ q) y = eval p y + eval q y := by
  simp [eval]

theorem eval_add (p q : Poly) (y : Fin 13 → ℝ) : eval (add p q) y = eval p y + eval q y := by
  rw [add, eval_normalize, eval_append]

theorem eval_neg (p : Poly) (y : Fin 13 → ℝ) : eval (neg p) y = -eval p y := by
  induction p with
  | nil => simp [neg, eval]
  | cons t p ih =>
    change qeval (qneg t.2) * wordEval t.1 y + eval (neg p) y = _
    rw [qeval_neg, ih]
    simp only [eval, List.map_cons, List.sum_cons]
    ring

theorem wordEval_insert (i : Fin 13) (w : Word) (y : Fin 13 → ℝ) :
    wordEval (wordInsert i w) y = y i * wordEval w y := by
  induction w with
  | nil => simp [wordInsert, wordEval]
  | cons j w ih =>
    simp only [wordInsert]
    split_ifs
    · simp [wordEval]
    · change y j * wordEval (wordInsert i w) y = _
      rw [ih]
      simp [wordEval]
      ring

theorem wordEval_sort (w : Word) (y : Fin 13 → ℝ) : wordEval (wordSort w) y = wordEval w y := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change wordEval (wordInsert i (wordSort w)) y = _
    rw [wordEval_insert, ih]
    rfl

theorem wordEval_sort_append (a b : Word) (y : Fin 13 → ℝ) :
    wordEval (wordSort (a ++ b)) y = wordEval a y * wordEval b y := by
  rw [wordEval_sort]
  simp [wordEval]

theorem eval_mul (p q : Poly) (y : Fin 13 → ℝ) : eval (mul p q) y = eval p y * eval q y := by
  rw [mul, eval_normalize]
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    simp only [List.flatMap_cons, eval_append, ih]
    have hm : eval (q.map fun s =>
        (wordSort (t.1 ++ s.1), qmul t.2 s.2)) y =
        qeval t.2 * wordEval t.1 y * eval q y := by
      clear ih
      induction q with
      | nil => simp [eval]
      | cons s q ihq =>
        simp only [List.map_cons, eval, List.sum_cons, qeval_mul,
          wordEval_sort_append] at *
        rw [ihq]
        ring
    rw [hm]
    simp only [eval, List.map_cons, List.sum_cons]
    ring

theorem wordEval_abs_le_one (w : Word) (y : Fin 13 → ℝ) (hy : ∀ j, |y j| ≤ 1) :
    |wordEval w y| ≤ 1 := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    change |y i * wordEval w y| ≤ 1
    rw [abs_mul]
    exact mul_le_one₀ (hy i) (abs_nonneg _) ih

theorem eval_abs_le (p : Poly) (y : Fin 13 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ t ∈ p, |qeval t.2| ≤ B) (hy : ∀ j, |y j| ≤ 1) :
    |eval p y| ≤ p.length * B := by
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    have ht := hp t (by simp)
    have hr := ih (fun s hs => hp s (by simp [hs]))
    have hw := wordEval_abs_le_one t.1 y hy
    have hm : |qeval t.2 * wordEval t.1 y| ≤ B := by
      rw [abs_mul]
      calc
        _ ≤ B * 1 := mul_le_mul ht hw (abs_nonneg _) hB
        _ = B := mul_one _
    change |qeval t.2 * wordEval t.1 y + eval p y| ≤ _
    have hh := abs_add_le (qeval t.2 * wordEval t.1 y) (eval p y)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem eval_scale (c : Q2) (p : Poly) (y : Fin 13 → ℝ) :
    eval (scale c p) y = qeval c * eval p y := by
  induction p with
  | nil => simp [scale, eval]
  | cons t p ih =>
    change qeval (qmul c t.2) * wordEval t.1 y + eval (scale c p) y = _
    rw [qeval_mul, ih]
    simp only [eval, List.map_cons, List.sum_cons]
    ring

theorem eval_weightedSquare (w : ℚ) (p : Poly) (y : Fin 13 → ℝ) :
    eval (weightedSquare w p) y = (w : ℝ) * eval p y ^ 2 := by
  rw [weightedSquare, eval_scale, eval_mul]
  simp [qeval, pow_two]

theorem eval_weightedSquare_nonneg (w : ℚ) (p : Poly) (hw : 0 ≤ w) (y : Fin 13 → ℝ) :
    0 ≤ eval (weightedSquare w p) y := by
  rw [eval_weightedSquare]
  exact mul_nonneg (by exact_mod_cast hw) (sq_nonneg _)

theorem eval_sum (ps : List Poly) (y : Fin 13 → ℝ) :
    eval (sum ps) y = (ps.map (fun p => eval p y)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change eval (add p (sum ps)) y = _
    rw [eval_add, ih]
    rfl

theorem eval_sum_nonneg (ps : List Poly) (hp : ∀ p ∈ ps, ∀ y, 0 ≤ eval p y)
    (y : Fin 13 → ℝ) : 0 ≤ eval (sum ps) y := by
  induction ps with
  | nil => simp [sum, eval]
  | cons p ps ih =>
    change 0 ≤ eval (add p (sum ps)) y
    rw [eval_add]
    exact add_nonneg (hp p (by simp) y) (ih (fun p h => hp p (by simp [h])))

def sqrtLower : ℚ := 1414213562373095048801688724209 / 1000000000000000000000000000000
def sqrtUpper : ℚ := 1414213562373095048801688724210 / 1000000000000000000000000000000

theorem sqrt_bracket : (sqrtLower : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (sqrtUpper : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  norm_num [sqrtLower, sqrtUpper]
  constructor <;> nlinarith

def bounded (c : Q2) (B : ℚ) : Prop :=
  -B ≤ c.1 + c.2 * sqrtLower ∧ c.1 + c.2 * sqrtLower ≤ B ∧
  -B ≤ c.1 + c.2 * sqrtUpper ∧ c.1 + c.2 * sqrtUpper ≤ B

instance (c : Q2) (B : ℚ) : Decidable (bounded c B) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem qeval_abs_le_of_bounded (c : Q2) (B : ℚ) (hc : bounded c B) : |qeval c| ≤ (B : ℝ) := by
  obtain ⟨h0,h1,h2,h3⟩ := hc
  have h0r : -(B : ℝ) ≤ (c.1 : ℝ) + (c.2 : ℝ) * (sqrtLower : ℝ) := by exact_mod_cast h0
  have h1r : (c.1 : ℝ) + (c.2 : ℝ) * (sqrtLower : ℝ) ≤ (B : ℝ) := by exact_mod_cast h1
  have h2r : -(B : ℝ) ≤ (c.1 : ℝ) + (c.2 : ℝ) * (sqrtUpper : ℝ) := by exact_mod_cast h2
  have h3r : (c.1 : ℝ) + (c.2 : ℝ) * (sqrtUpper : ℝ) ≤ (B : ℝ) := by exact_mod_cast h3
  obtain ⟨hl,hu⟩ := sqrt_bracket
  rw [abs_le]
  dsimp [qeval]
  rcases le_total 0 (c.2 : ℝ) with hcpos | hcneg
  · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hcpos, mul_le_mul_of_nonneg_left hu hcpos]
  · constructor <;> nlinarith [mul_le_mul_of_nonpos_left hl hcneg, mul_le_mul_of_nonpos_left hu hcneg]

#print axioms eval_mul
#print axioms eval_abs_le
#print axioms qeval_abs_le_of_bounded
end Blueprint.CAP.BoundaryDirect
