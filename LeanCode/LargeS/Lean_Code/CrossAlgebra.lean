import Lean_Code.SphericalStrictMetric

set_option maxHeartbeats 1000000
open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma cross_inner_cross (x y z w : ℝ³) :
    inner ℝ (crossVec x y) (crossVec z w) =
      inner ℝ x z * inner ℝ y w - inner ℝ x w * inner ℝ y z := by
  simp only [inner_coordinate_sum]
  simp [crossVec, Fin.sum_univ_succ]
  ring

lemma crossVec_smul_left (a : ℝ) (x y : ℝ³) : crossVec (a • x) y = a • crossVec x y := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

lemma crossVec_smul_right (a : ℝ) (x y : ℝ³) : crossVec x (a • y) = a • crossVec x y := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

lemma triple_cyclic (x y z : ℝ³) :
    inner ℝ (crossVec x y) z = inner ℝ (crossVec y z) x := by
  simp only [inner_coordinate_sum]
  simp [crossVec, Fin.sum_univ_succ]
  ring

lemma cross_cross_cyclic (x y z : ℝ³) :
    crossVec (crossVec x y) (crossVec y z) = inner ℝ (crossVec x y) z • y := by
  ext i
  fin_cases i <;> simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ] <;> ring

lemma cross_normal_triple (x y z : ℝ³) :
    inner ℝ (crossVec (crossVec x y) (crossVec y z)) (crossVec z x) =
      inner ℝ (crossVec x y) z ^ 2 := by
  rw [cross_cross_cyclic, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [real_inner_comm (crossVec z x) y, ← triple_cyclic y z x, ← triple_cyclic x y z]
  ring

def sphereEdgeNormal (x y : ℝ³) : ℝ³ := ‖crossVec x y‖⁻¹ • crossVec x y

lemma sphereEdgeNormal_unit (x y : ℝ³) (hne : crossVec x y ≠ 0) :
    ‖sphereEdgeNormal x y‖ = 1 := by
  have hp : 0 < ‖crossVec x y‖ := norm_pos_iff.mpr hne
  simp [sphereEdgeNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), hp.ne']

lemma triple_nonzero_cross (x y z : ℝ³) (h : inner ℝ (crossVec x y) z ≠ 0) :
    crossVec x y ≠ 0 ∧ crossVec y z ≠ 0 ∧ crossVec z x ≠ 0 := by
  have h1 : crossVec x y ≠ 0 := by intro hc; exact h (by rw [hc, inner_zero_left])
  have h2 : crossVec y z ≠ 0 := by intro hc; exact h (by rw [triple_cyclic, hc, inner_zero_left])
  have h3 : crossVec z x ≠ 0 := by intro hc; exact h (by rw [triple_cyclic, triple_cyclic, hc, inner_zero_left])
  exact ⟨h1, h2, h3⟩

theorem edge_normals_nondegenerate (x y z : ℝ³) (h : inner ℝ (crossVec x y) z ≠ 0) :
    inner ℝ (crossVec (sphereEdgeNormal x y) (sphereEdgeNormal y z)) (sphereEdgeNormal z x) ≠ 0 := by
  obtain ⟨hxy, hyz, hzx⟩ := triple_nonzero_cross x y z h
  have hnx : ‖crossVec x y‖ ≠ 0 := norm_ne_zero_iff.mpr hxy
  have hny : ‖crossVec y z‖ ≠ 0 := norm_ne_zero_iff.mpr hyz
  have hnz : ‖crossVec z x‖ ≠ 0 := norm_ne_zero_iff.mpr hzx
  simp only [sphereEdgeNormal, crossVec_smul_left, crossVec_smul_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, cross_normal_triple]
  exact mul_ne_zero (inv_ne_zero hnz) (mul_ne_zero (inv_ne_zero hny) (mul_ne_zero (inv_ne_zero hnx) (pow_ne_zero 2 h)))

end SquareAntiprismVerification
