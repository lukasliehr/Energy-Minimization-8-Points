import Lean_Code.ContactAngles
import Lean_Code.PackingMaximum

set_option maxHeartbeats 1500000
set_option maxRecDepth 3000

open Real
open scoped Matrix
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def gramFour (Y : Fin 4 → ℝ³) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => inner ℝ (Y i) (Y j)

lemma gramFour_det_zero (Y : Fin 4 → ℝ³) : (gramFour Y).det = 0 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := fun i => ![Y i 0, Y i 1, Y i 2, 0]
  have hzero : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 3 (by intro i; rfl)
  have hgram : gramFour Y = A * A.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp [gramFour, A, Matrix.transpose, inner_coordinate_sum, Fin.sum_univ_succ]
  rw [hgram, Matrix.det_mul, hzero, zero_mul]

def rhombusGram (c x y : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, c, x, c], ![c, 1, c, y], ![x, c, 1, c], ![c, y, c, 1]]

lemma rhombusGram_det (c x y : ℝ) :
    (rhombusGram c x y).det = (1 - x) * (1 - y) * ((1 + x) * (1 + y) - 4 * c ^ 2) := by
  rw [Matrix.det_succ_row_zero]
  simp [rhombusGram, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

lemma unit_inner_lt_one (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    inner ℝ x y < 1 := by
  have h := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  rw [sphere_sq_distance x y hx hy] at h
  linarith

/-- The exact diagonal identity of an equilateral spherical quadrilateral.
It follows from the rank-three Gram determinant, without a geometric
classification or a spherical-area formula. -/
theorem rhombus_diagonal_identity (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (h02 : Y 0 ≠ Y 2) (h13 : Y 1 ≠ Y 3)
    (h01 : inner ℝ (Y 0) (Y 1) = c) (h12 : inner ℝ (Y 1) (Y 2) = c)
    (h23 : inner ℝ (Y 2) (Y 3) = c) (h30 : inner ℝ (Y 3) (Y 0) = c) :
    (1 + inner ℝ (Y 0) (Y 2)) * (1 + inner ℝ (Y 1) (Y 3)) = 4 * c ^ 2 := by
  have h10 : inner ℝ (Y 1) (Y 0) = c := (real_inner_comm (Y 0) (Y 1)).trans h01
  have h21 : inner ℝ (Y 2) (Y 1) = c := (real_inner_comm (Y 1) (Y 2)).trans h12
  have h32 : inner ℝ (Y 3) (Y 2) = c := (real_inner_comm (Y 2) (Y 3)).trans h23
  have h03 : inner ℝ (Y 0) (Y 3) = c := (real_inner_comm (Y 3) (Y 0)).trans h30
  have h20 : inner ℝ (Y 2) (Y 0) = inner ℝ (Y 0) (Y 2) := real_inner_comm (Y 0) (Y 2)
  have h31 : inner ℝ (Y 3) (Y 1) = inner ℝ (Y 1) (Y 3) := real_inner_comm (Y 1) (Y 3)
  have hgram : gramFour Y = rhombusGram c (inner ℝ (Y 0) (Y 2)) (inner ℝ (Y 1) (Y 3)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gramFour, rhombusGram, hY, h01, h12, h23, h30, h10, h21, h32, h03, h20, h31]
  have hdet := gramFour_det_zero Y
  rw [hgram, rhombusGram_det] at hdet
  have hx : 1 - inner ℝ (Y 0) (Y 2) ≠ 0 := by
    linarith [unit_inner_lt_one _ _ (hY 0) (hY 2) h02]
  have hy : 1 - inner ℝ (Y 1) (Y 3) ≠ 0 := by
    linarith [unit_inner_lt_one _ _ (hY 1) (hY 3) h13]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left (mul_ne_zero hx hy))

lemma rhombus_diagonals_short_scalar (c x y : ℝ) (hc : 0 < c)
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) (hy : y ∈ Set.Ico (-1 : ℝ) 1)
    (hrel : (1 + x) * (1 + y) = 4 * c ^ 2) :
    2 * c ^ 2 - 1 < x ∧ 2 * c ^ 2 - 1 < y := by
  have hxpos : 0 < 1 + x := by
    by_contra h
    have hz : 1 + x = 0 := by linarith [hx.1]
    rw [hz, zero_mul] at hrel
    nlinarith [sq_pos_of_pos hc]
  have hypos : 0 < 1 + y := by
    by_contra h
    have hz : 1 + y = 0 := by linarith [hy.1]
    rw [hz, mul_zero] at hrel
    nlinarith [sq_pos_of_pos hc]
  have h₁ := mul_pos hxpos (by linarith [hy.2] : 0 < 1 - y)
  have h₂ := mul_pos hypos (by linarith [hx.2] : 0 < 1 - x)
  constructor <;> nlinarith

end SquareAntiprismVerification
