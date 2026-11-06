import AllS.Units.N_AI.N_matrix_polynomials.N_bernstein_identity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def gramFromFactors {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  δ • (K*K.transpose) + ∑ j, bernsteinWeight d j.val x • (F j*(F j).transpose)

def GramUncorrectedFloorStatement : Prop :=
  ∀ {n d : ℕ} (δ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ),
    0 < δ → K.IsLowerTriangular → (∀ i, 0 < K i i) →
    ∀ x ∈ cellDomain,
      (gramFromFactors δ K F x - δ • (K*K.transpose)).PosSemidef ∧
      (gramFromFactors δ K F x).PosDef

theorem matrix_square_posSemidef {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) :
    (K*K.transpose).PosSemidef := by
  simpa using Matrix.posSemidef_self_mul_conjTranspose K

theorem lower_triangular_isUnit {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.IsLowerTriangular) (hdiag : ∀ i, K i i ≠ 0) : IsUnit K := by
  apply (Matrix.isUnit_iff_isUnit_det K).mpr
  rw [Matrix.det_of_isLowerTriangular K hK]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

theorem matrix_square_posDef {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : IsUnit K) : (K*K.transpose).PosDef := by
  simpa using Matrix.PosDef.mul_conjTranspose_self K
    (Matrix.vecMul_injective_iff_isUnit.mpr hK)

theorem gram_bernstein_remainder_posSemidef {n d : ℕ}
    (F : Fin (d+1) → Matrix (Fin n) (Fin n) ℝ) (x : ℝ) (hx : x ∈ cellDomain) :
    (∑ j, bernsteinWeight d j.val x • (F j*(F j).transpose)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  exact (matrix_square_posSemidef (F j)).smul (bernsteinWeight_nonneg d j.val x hx)

theorem gram_replay_uncorrected_floor : GramUncorrectedFloorStatement := by
  intro n d δ K F hδ hK hdiag x hx
  have hrem := gram_bernstein_remainder_posSemidef F x hx
  have hbase := (matrix_square_posDef K
    (lower_triangular_isUnit K hK (fun i => ne_of_gt (hdiag i)))).smul hδ
  constructor
  · simpa only [gramFromFactors, add_sub_cancel_left] using hrem
  · exact hbase.add_posSemidef hrem

#print GramUncorrectedFloorStatement
#print axioms gram_replay_uncorrected_floor
end Blueprint.CAP
