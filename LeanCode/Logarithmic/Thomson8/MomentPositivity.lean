import Thomson8.BlockValue
import Thomson8.RCounting
import Thomson8.MatrixPairing

namespace Thomson8.Block

open scoped InnerProductSpace

theorem moment_total (b : Block) (hm : b.moment=true) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y b.value) =
      6*∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
        b.F a c*momentMatrix b.basis.length b.k y a c := by
  unfold onTriples
  simp_rw [moment_value b hm,distinctSum_fin_sum,distinctSum_mul]
  change (∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
    b.F a c*distinctSum (onTriples y (R b.k a c).eval)) = _
  simp_rw [sum_R_eq_moment _ _ y hy]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem moment_total_nonneg (b : Block) (hm : b.moment=true) (hb : b.matrix.PosSemidef)
    (y : Configuration) (hy : ∀ i, ‖y i‖=1) : 0 ≤ distinctSum (onTriples y b.value) := by
  rw [moment_total b hm y hy]
  exact mul_nonneg (by norm_num) (matrix_pairing_nonneg _ _ (b.F_posSemidef hb)
    (momentMatrix_posSemidef _ _ y hy))

#print axioms moment_total_nonneg

end Thomson8.Block
