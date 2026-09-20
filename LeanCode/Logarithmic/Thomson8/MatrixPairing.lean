import Thomson8.Positivity
import Mathlib.Analysis.Matrix.Order

namespace Thomson8

theorem matrix_pairing_nonneg {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ ∑ i, ∑ j, A i j*B i j := by
  have h := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => 1)
  simpa [Matrix.mulVec,dotProduct] using h

theorem quadratic_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (x : ι → ℝ) : 0 ≤ quadratic A x := by
  simpa only [quadratic,Matrix.mulVec,dotProduct,star_trivial,Finset.mul_sum,mul_assoc] using
    hA.dotProduct_mulVec_nonneg x

end Thomson8
