import Lean_Code.SphericalMetric

set_option maxHeartbeats 1500000
open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma triple_gram_identity (x y z : ℝ³) :
    inner ℝ (crossVec x y) z ^ 2 =
      inner ℝ x x * inner ℝ y y * inner ℝ z z +
        2 * inner ℝ x y * inner ℝ y z * inner ℝ x z -
        inner ℝ x x * inner ℝ y z ^ 2 - inner ℝ y y * inner ℝ x z ^ 2 -
        inner ℝ z z * inner ℝ x y ^ 2 := by
  simp only [inner_coordinate_sum]
  simp [crossVec, Fin.sum_univ_succ]
  ring

lemma unit_triple_gram_identity (x y z : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    inner ℝ (crossVec x y) z ^ 2 =
      1 + 2 * inner ℝ x y * inner ℝ y z * inner ℝ x z -
        inner ℝ y z ^ 2 - inner ℝ x z ^ 2 - inner ℝ x y ^ 2 := by
  rw [triple_gram_identity]
  simp [hx, hy, hz]

lemma sphereAngle_cos_add_strict (x y z : ℝ³)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (htriple : inner ℝ (crossVec x y) z ≠ 0) :
    Real.cos (sphereAngle x y + sphereAngle y z) < inner ℝ x z := by
  have hle := sphereAngle_cos_add_bound x y z hx hy hz
  refine lt_of_le_of_ne hle ?_
  intro heq
  have ha := Real.sin_sq_add_cos_sq (sphereAngle x y)
  have hb := Real.sin_sq_add_cos_sq (sphereAngle y z)
  rw [cos_sphereAngle x y hx hy] at ha
  rw [cos_sphereAngle y z hy hz] at hb
  rw [Real.cos_add, cos_sphereAngle x y hx hy, cos_sphereAngle y z hy hz] at heq
  have hgram := unit_triple_gram_identity x y z hx hy hz
  have hprod : (Real.sin (sphereAngle x y) * Real.sin (sphereAngle y z)) ^ 2 =
      (1 - inner ℝ x y ^ 2) * (1 - inner ℝ y z ^ 2) := by
    rw [mul_pow]
    have ha' : Real.sin (sphereAngle x y) ^ 2 = 1 - inner ℝ x y ^ 2 := by linarith
    have hb' : Real.sin (sphereAngle y z) ^ 2 = 1 - inner ℝ y z ^ 2 := by linarith
    rw [ha', hb']
  have hd : inner ℝ x z - inner ℝ x y * inner ℝ y z =
      -(Real.sin (sphereAngle x y) * Real.sin (sphereAngle y z)) := by linarith
  have hdsq := congrArg (fun t : ℝ => t ^ 2) hd
  nlinarith [sq_pos_of_ne_zero htriple]

theorem sphereAngle_triangle_strict (x y z : ℝ³)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (htriple : inner ℝ (crossVec x y) z ≠ 0) :
    sphereAngle x z < sphereAngle x y + sphereAngle y z := by
  refine lt_of_le_of_ne (sphereAngle_triangle x y z hx hy hz) ?_
  intro heq
  have hstrict := sphereAngle_cos_add_strict x y z hx hy hz htriple
  rw [← heq, cos_sphereAngle x z hx hz] at hstrict
  exact lt_irrefl _ hstrict

lemma crossVec_neg_right (x y : ℝ³) : crossVec x (-y) = -crossVec x y := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

theorem sphere_triangle_perimeter_strict (x y z : ℝ³)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (htriple : inner ℝ (crossVec x y) z ≠ 0) :
    sphereAngle x y + sphereAngle y z + sphereAngle z x < 2 * Real.pi := by
  have htriple' : inner ℝ (crossVec x (-y)) z ≠ 0 := by
    simpa [crossVec_neg_right, inner_neg_left] using htriple
  have h := sphereAngle_triangle_strict x (-y) z hx (by simpa using hy) hz htriple'
  rw [sphereAngle_neg_right, sphereAngle_comm (-y) z, sphereAngle_neg_right,
    sphereAngle_comm z y] at h
  rw [sphereAngle_comm z x]
  linarith

end SquareAntiprismVerification
