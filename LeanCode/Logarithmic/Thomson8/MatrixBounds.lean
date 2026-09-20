import Thomson8.Data
import Thomson8.LogCache
import Thomson8.Positivity

namespace Thomson8
namespace Box

def sumFin (n : ℕ) (f : Fin n → Box) : Box := sum (List.ofFn f)

theorem contains_sumFin (n : ℕ) (f : Fin n → Box) (g : Fin n → ℝ)
    (h : ∀ i, (f i).Contains (g i)) : (sumFin n f).Contains (∑ i, g i) := by
  induction n with
  | zero => simp [sumFin, sum, Contains, exact]
  | succ n ih =>
    simpa only [sumFin, List.ofFn_succ, sum, Fin.sum_univ_succ] using
      contains_add (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

def matmul (n : ℕ) (a b : Matrix (Fin n) (Fin n) Box) : Matrix (Fin n) (Fin n) Box :=
  fun i j => sumFin n (fun k => times (a i k) (b k j))

theorem contains_matmul (n : ℕ) (a b : Matrix (Fin n) (Fin n) Box)
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, (a i j).Contains (A i j)) (hb : ∀ i j, (b i j).Contains (B i j)) :
    ∀ i j, (matmul n a b i j).Contains ((A*B) i j) := by
  intro i j
  apply contains_sumFin
  intro k
  exact contains_times (ha i k) (hb k j)

def magnitude (b : Box) : ℚ := max |b.lo| |b.hi|

theorem abs_le_magnitude {b : Box} {x : ℝ} (hx : b.Contains x) : |x| ≤ (b.magnitude : ℝ) := by
  simp only [magnitude, Rat.cast_max, Rat.cast_abs]
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hx.1)
  · exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))

def rowError (n : ℕ) (c : Matrix (Fin n) (Fin n) Box) (i : Fin n) : ℚ :=
  (List.ofFn fun j : Fin n => (sub (c i j) (exact (if i=j then 1 else 0))).magnitude).sum

theorem rowError_bound (n : ℕ) (c : Matrix (Fin n) (Fin n) Box)
    (C : Matrix (Fin n) (Fin n) ℝ) (hc : ∀ i j, (c i j).Contains (C i j)) (i : Fin n) :
    (∑ j, |C i j - (if i=j then 1 else 0)|) ≤ (rowError n c i : ℝ) := by
  simp only [rowError, List.sum_ofFn, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro j _
  have h : (exact (if i=j then (1 : ℚ) else 0)).Contains (if i=j then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num [Contains, exact]
  exact abs_le_magnitude (contains_sub (hc i j) h)

end Box

namespace Block

noncomputable def matrix (b : Block) : Matrix (Fin b.n) (Fin b.n) ℝ :=
  fun i j => ∑ ell : Fin 5, logValues ell * (b.entry i j ell).eval

def matrixBox (b : Block) : Matrix (Fin b.n) (Fin b.n) Box :=
  fun i j => Box.sumFin 5 (fun ell => Box.times (cachedLogs ell) (encloseK (b.entry i j ell)))

theorem matrixBox_contains (b : Block) (i j : Fin b.n) :
    (b.matrixBox i j).Contains (b.matrix i j) := by
  apply Box.contains_sumFin
  intro ell
  exact Box.contains_times (cachedLogs_contains ell) (encloseK_contains _)

theorem matrix_symmetric (b : Block) (i j : Fin b.n) : b.matrix i j = b.matrix j i := by
  simp only [matrix, entry, min_comm i.val j.val, max_comm i.val j.val]

def preconditionerEntry (b : Block) (i j : Fin b.n) : ℚ :=
  (b.preconditioner.getD i []).getD j 0

noncomputable def P (b : Block) : Matrix (Fin b.n) (Fin b.n) ℝ :=
  fun i j => (b.preconditionerEntry i j : ℝ)
def PBox (b : Block) : Matrix (Fin b.n) (Fin b.n) Box :=
  fun i j => Box.rational (b.preconditionerEntry i j)

theorem PBox_contains (b : Block) (i j : Fin b.n) : (b.PBox i j).Contains (b.P i j) :=
  Box.contains_rational _

def congruenceBox (b : Block) : Matrix (Fin b.n) (Fin b.n) Box :=
  Box.matmul b.n (Box.matmul b.n b.PBox b.matrixBox) b.PBox.transpose

theorem congruenceBox_contains (b : Block) (i j : Fin b.n) :
    (b.congruenceBox i j).Contains ((b.P*b.matrix*b.P.transpose) i j) :=
  Box.contains_matmul _ _ _ _ _
    (Box.contains_matmul _ _ _ _ _ b.PBox_contains b.matrixBox_contains)
    (fun i j => b.PBox_contains j i) i j

abbrev PositiveCheck (b : Block) : Prop := ∀ i : Fin b.n,
  Box.rowError b.n b.congruenceBox i ≤ 1/2

theorem positive_of_enclosure (b : Block) (c : Matrix (Fin b.n) (Fin b.n) Box)
    (hc : ∀ i j, (c i j).Contains ((b.P*b.matrix*b.P.transpose) i j))
    (h : ∀ i, Box.rowError b.n c i ≤ 1/2) : b.matrix.PosDef := by
  apply posDef_of_congruence b.P b.matrix
  apply posDef_of_row_bound
  · have hb : b.matrix.IsHermitian := by
      ext i j
      simpa using b.matrix_symmetric j i
    have hc := Matrix.isHermitian_conjTranspose_mul_mul b.P.transpose hb
    intro i j
    have hce := congrFun (congrFun hc i) j
    simpa using hce.symm
  · intro i
    apply (Box.rowError_bound _ _ _ hc i).trans
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (h i)

theorem positiveCheck_sound (b : Block) (h : b.PositiveCheck) : b.matrix.PosDef :=
  b.positive_of_enclosure b.congruenceBox b.congruenceBox_contains h

end Block
end Thomson8
