import Coulomb8.BlockValue
import Thomson8.RCounting
import Thomson8.MatrixPairing

namespace Coulomb8.Block

open scoped InnerProductSpace
open Thomson8 (distinctSum onTriples momentMatrix distinctSum_fin_sum distinctSum_mul matrix_pairing_nonneg momentMatrix_posSemidef)

theorem moment_total (b : Block) (w : Fin 192 → ℝ) (hm : b.moment=true) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (b.value w)) =
      6*∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
        b.momentF w a c*momentMatrix b.basis.length b.k y a c := by
  unfold onTriples
  simp_rw [moment_value b w hm,distinctSum_fin_sum,distinctSum_mul]
  change (∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
    b.momentF w a c*distinctSum (onTriples y (R b.k a c).eval)) = _
  simp_rw [sum_R_eq_moment _ _ y hy]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem moment_total_nonneg (b : Block) (w : Fin 192 → ℝ) (hm : b.moment=true) (hb : (b.matrixFrom w).PosSemidef)
    (y : Configuration) (hy : ∀ i, ‖y i‖=1) : 0 ≤ distinctSum (onTriples y (b.value w)) := by
  rw [moment_total b w hm y hy]
  exact mul_nonneg (by norm_num) (matrix_pairing_nonneg _ _ (b.F_posSemidef w hb)
    (momentMatrix_posSemidef _ _ y hy))

#print axioms moment_total_nonneg

end Coulomb8.Block
