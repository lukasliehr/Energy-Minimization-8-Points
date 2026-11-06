import Mathlib

noncomputable section
open scoped BigOperators
namespace ThomsonNegative

/-- Triangular dyadic factors need no numerical inverse certificate. -/
theorem triangular_det_pos (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (htri : ∀ i j, i<j → J i j=0) (hdiag : ∀ i, 0<J i i) : 0<J.det := by
  have h : J.BlockTriangular OrderDual.toDual := fun {_ _} hij => htri _ _ hij
  rw [Matrix.det_of_lowerTriangular J h]
  exact Finset.prod_pos (fun i _ => hdiag i)

theorem triangular_isUnit (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (htri : ∀ i j, i<j → J i j=0) (hdiag : ∀ i, 0<J i i) : IsUnit J := by
  exact (Matrix.isUnit_iff_isUnit_det J).mpr
    (isUnit_iff_ne_zero.mpr (triangular_det_pos n J htri hdiag).ne')

/-- Every proposed lower-triangular positive-diagonal factor gives an exactly
positive Gram, irrespective of how its entries were proposed. -/
theorem triangular_gram_posDef (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (htri : ∀ i j, i<j → J i j=0) (hdiag : ∀ i, 0<J i i) :
    (J*J.transpose).PosDef := by
  have hJ := triangular_isUnit n J htri hdiag
  have h := (Matrix.PosDef.one (n := Fin n) (R := ℝ)).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hJ)
  simpa using h

#print axioms triangular_gram_posDef
end ThomsonNegative
