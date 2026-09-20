import Lean_Code.CrossAlgebra

set_option maxHeartbeats 1000000
open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma crossVec_swap (x y : ℝ³) : crossVec y x = -crossVec x y := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

lemma crossVec_norm_comm (x y : ℝ³) : ‖crossVec y x‖ = ‖crossVec x y‖ := by
  rw [crossVec_swap, norm_neg]

def sphereTangent (p q : ℝ³) : ℝ³ :=
  ‖crossVec p q‖⁻¹ • (q - inner ℝ p q • p)

def sphereVertexAngle (p q r : ℝ³) : ℝ := sphereAngle (sphereTangent p q) (sphereTangent p r)

lemma projection_norm_cross (p q : ℝ³) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖q - inner ℝ p q • p‖ = ‖crossVec p q‖ := by
  have hproj := unit_projection_norm_sq q p hq hp
  rw [real_inner_comm p q] at hproj
  have hcross := crossVec_norm_sq p q
  rw [hp, hq] at hcross
  nlinarith [norm_nonneg (q - inner ℝ p q • p), norm_nonneg (crossVec p q)]

lemma sphereTangent_unit (p q : ℝ³) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hne : crossVec p q ≠ 0) :
    ‖sphereTangent p q‖ = 1 := by
  have hnorm : ‖crossVec p q‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  simp [sphereTangent, norm_smul, projection_norm_cross p q hp hq, hnorm]

lemma edge_normals_tangent_inner (p q r : ℝ³) (hp : ‖p‖ = 1) :
    inner ℝ (sphereEdgeNormal r p) (sphereEdgeNormal p q) =
      -inner ℝ (sphereTangent p q) (sphereTangent p r) := by
  simp only [sphereEdgeNormal, sphereTangent, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, cross_inner_cross]
  have hproj := unit_projection_inner q p r hp
  rw [real_inner_comm p q, real_inner_comm p r] at hproj
  rw [hproj, real_inner_self_eq_norm_sq, hp, real_inner_comm p r,
    real_inner_comm q r, crossVec_norm_comm p r]
  ring

theorem vertex_angle_polar_identity (p q r : ℝ³) (hp : ‖p‖ = 1) :
    sphereAngle (sphereEdgeNormal r p) (sphereEdgeNormal p q) = Real.pi - sphereVertexAngle p q r := by
  unfold sphereAngle sphereVertexAngle
  rw [edge_normals_tangent_inner p q r hp, Real.arccos_neg]
  rfl

theorem spherical_triangle_excess_positive (p q r : ℝ³)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hnondeg : inner ℝ (crossVec p q) r ≠ 0) :
    Real.pi < sphereVertexAngle p q r + sphereVertexAngle q r p + sphereVertexAngle r p q := by
  obtain ⟨hpq, hqr, hrp⟩ := triple_nonzero_cross p q r hnondeg
  have hperim := sphere_triangle_perimeter_strict (sphereEdgeNormal p q) (sphereEdgeNormal q r)
    (sphereEdgeNormal r p) (sphereEdgeNormal_unit p q hpq) (sphereEdgeNormal_unit q r hqr)
    (sphereEdgeNormal_unit r p hrp) (edge_normals_nondegenerate p q r hnondeg)
  rw [vertex_angle_polar_identity q r p hq, vertex_angle_polar_identity r p q hr,
    vertex_angle_polar_identity p q r hp] at hperim
  linarith

end SquareAntiprismVerification
