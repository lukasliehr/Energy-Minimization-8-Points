import Lean_Code.ContactDirections

set_option maxHeartbeats 1000000
open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sphereAngle (x y : ℝ³) : ℝ := Real.arccos (inner ℝ x y)

lemma unit_inner_mem_Icc (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ x y ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, one_mul] at h
  exact abs_le.mp h

lemma sphereAngle_range (x y : ℝ³) : sphereAngle x y ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma cos_sphereAngle (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.cos (sphereAngle x y) = inner ℝ x y := by
  have h := unit_inner_mem_Icc x y hx hy
  exact Real.cos_arccos h.1 h.2

lemma sphereAngle_comm (x y : ℝ³) : sphereAngle x y = sphereAngle y x := by
  unfold sphereAngle
  rw [real_inner_comm x y]

lemma unit_projection_inner (x y z : ℝ³) (hy : ‖y‖ = 1) :
    inner ℝ (x - inner ℝ x y • y) (z - inner ℝ z y • y) =
      inner ℝ x z - inner ℝ x y * inner ℝ y z := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [real_inner_self_eq_norm_sq, hy, real_inner_comm y z]
  ring

lemma unit_projection_norm_sq (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - inner ℝ x y • y‖ ^ 2 = 1 - inner ℝ x y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, unit_projection_inner x y x hy, real_inner_comm x y]
  simp [hx, pow_two]

lemma unit_projection_norm (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - inner ℝ x y • y‖ = Real.sin (sphereAngle x y) := by
  have hn := unit_projection_norm_sq x y hx hy
  have htrig := Real.sin_sq_add_cos_sq (sphereAngle x y)
  rw [cos_sphereAngle x y hx hy] at htrig
  have hsin := Real.sin_nonneg_of_mem_Icc (sphereAngle_range x y)
  nlinarith [norm_nonneg (x - inner ℝ x y • y)]

lemma sphereAngle_cos_add_bound (x y z : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    Real.cos (sphereAngle x y + sphereAngle y z) ≤ inner ℝ x z := by
  have hb := (abs_le.mp (abs_real_inner_le_norm (x - inner ℝ x y • y) (z - inner ℝ z y • y))).1
  rw [unit_projection_inner x y z hy, unit_projection_norm x y hx hy,
    unit_projection_norm z y hz hy, sphereAngle_comm z y] at hb
  rw [Real.cos_add, cos_sphereAngle x y hx hy, cos_sphereAngle y z hy hz]
  linarith

theorem sphereAngle_triangle (x y z : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    sphereAngle x z ≤ sphereAngle x y + sphereAngle y z := by
  by_cases hsum : Real.pi ≤ sphereAngle x y + sphereAngle y z
  · exact (sphereAngle_range x z).2.trans hsum
  have hsumI : sphereAngle x y + sphereAngle y z ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨add_nonneg (sphereAngle_range x y).1 (sphereAngle_range y z).1, (lt_of_not_ge hsum).le⟩
  by_contra h
  have hcos := Real.strictAntiOn_cos hsumI (sphereAngle_range x z) (lt_of_not_ge h)
  rw [cos_sphereAngle x z hx hz] at hcos
  linarith [sphereAngle_cos_add_bound x y z hx hy hz]

lemma sphereAngle_neg_right (x y : ℝ³) : sphereAngle x (-y) = Real.pi - sphereAngle x y := by
  simp only [sphereAngle, inner_neg_right, Real.arccos_neg]

theorem sphere_triangle_perimeter (x y z : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    sphereAngle x y + sphereAngle y z + sphereAngle z x ≤ 2 * Real.pi := by
  have h := sphereAngle_triangle x (-y) z hx (by simpa using hy) hz
  rw [sphereAngle_neg_right, sphereAngle_comm (-y) z, sphereAngle_neg_right,
    sphereAngle_comm z y] at h
  rw [sphereAngle_comm z x]
  linarith

end SquareAntiprismVerification
