import AllS.Units.N_AI.N_correction_bounds.N_weighted_quadratic
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def CorrectionFloorSupportStatement : Prop :=
  ∀ {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℝ) (δ γ : ℝ),
    G.IsHermitian → E.IsHermitian →
    (∀ v, δ*squaredEuclidean v ≤ quadratic G v) →
    QuadraticBound E γ → γ < δ → (G+E).PosDef

theorem quadratic_eq_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : quadratic M v = dotProduct (star v) (Matrix.mulVec M v) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_add {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : quadratic (G+E) v = quadratic G v + quadratic E v := by
  simp [quadratic, mul_add, add_mul, Finset.sum_add_distrib]

theorem squaredEuclidean_pos {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < squaredEuclidean v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  unfold squaredEuclidean
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem correctionFloorSupport : CorrectionFloorSupportStatement := by
  intro n G E δ γ hG hE hfloor hbound hγ
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hG.add hE)
  intro v hv
  rw [←quadratic_eq_dotProduct, quadratic_add]
  have hnorm := squaredEuclidean_pos v hv
  have he := (abs_le.mp (hbound.2 v)).1
  have hpos := mul_pos (sub_pos.mpr hγ) hnorm
  have hg := hfloor v
  nlinarith

#print CorrectionFloorSupportStatement
#print axioms correctionFloorSupport
end Blueprint.CAP
