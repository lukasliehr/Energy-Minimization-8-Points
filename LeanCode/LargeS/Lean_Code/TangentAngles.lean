import Lean_Code.TangentCircle

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma planar_rotation_unit (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hxy : x ^ 2 + y ^ 2 = 1) :
    (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 = 1 := by
  calc
    _ = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by ring
    _ = 1 := by rw [hab, hxy, one_mul]

lemma planar_rotation_dot (a b x y u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (a * x + b * y) * (a * u + b * v) +
      (a * y - b * x) * (a * v - b * u) = x * u + y * v := by
  linear_combination (x * u + y * v) * hab

lemma planar_rotation_det (a b x y u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (a * x + b * y) * (a * v - b * u) -
      (a * y - b * x) * (a * u + b * v) = x * v - y * u := by
  linear_combination (x * v - y * u) * hab

theorem upper_circle_angle_add (x y u v : ℝ)
    (hxy : x ^ 2 + y ^ 2 = 1) (huv : u ^ 2 + v ^ 2 = 1)
    (hy : 0 < y) (hv : 0 < v) (hdet : 0 < x * v - y * u) :
    Real.arccos x + Real.arccos (x * u + y * v) = Real.arccos u := by
  have hphase1 : circlePhase x y = Real.arccos x := by simp [circlePhase, hy.le]
  have hphase2 : circlePhase u v = Real.arccos u := by simp [circlePhase, hv.le]
  have hs1 := circlePhase_sin x y hxy
  have hc1 := circlePhase_cos x y hxy
  have hs2 := circlePhase_sin u v huv
  have hc2 := circlePhase_cos u v huv
  rw [hphase1] at hs1 hc1
  rw [hphase2] at hs2 hc2
  have hsin : 0 < Real.sin (Real.arccos u - Real.arccos x) := by
    rw [Real.sin_sub, hs2, hc1, hc2, hs1]
    nlinarith
  have hdelta : 0 < Real.arccos u - Real.arccos x := by
    by_contra hn
    have hs := Real.sin_nonneg_of_mem_Icc
      (show -(Real.arccos u - Real.arccos x) ∈ Set.Icc (0 : ℝ) Real.pi from
        ⟨by linarith, by linarith [Real.arccos_nonneg u, Real.arccos_le_pi x]⟩)
    rw [Real.sin_neg] at hs
    linarith
  have hle : Real.arccos u - Real.arccos x ≤ Real.pi := by
    linarith [Real.arccos_le_pi u, Real.arccos_nonneg x]
  have hcos : x * u + y * v = Real.cos (Real.arccos u - Real.arccos x) := by
    rw [Real.cos_sub, hc1, hc2, hs1, hs2]
    ring
  rw [hcos, Real.arccos_cos hdelta.le hle]
  ring

lemma tangent_inner_coordinates (p v w : ℝ³) (hp : ‖p‖ = 1)
    (hpv : inner ℝ p v = 0) (hpw : inner ℝ p w = 0) :
    inner ℝ v w = tangentCircleAlign p v 0 * tangentCircleAlign p w 0 +
      tangentCircleAlign p v 1 * tangentCircleAlign p w 1 := by
  rw [← (tangentCircleAlign p).inner_map_map v w, inner_coordinate_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change tangentCircleAlign p v 0 * tangentCircleAlign p w 0 +
    (tangentCircleAlign p v 1 * tangentCircleAlign p w 1 +
      tangentCircleAlign p v 2 * tangentCircleAlign p w 2) = _
  rw [tangentCircleAlign_last p v hp hpv, zero_mul, add_zero]

lemma tangent_triple_coordinates (p v w : ℝ³) (hp : ‖p‖ = 1) :
    inner ℝ (crossVec v w) p = tangentCircleAlign p v 0 * tangentCircleAlign p w 1 -
      tangentCircleAlign p v 1 * tangentCircleAlign p w 0 := by
  rw [← (tangentCircleAlign p).inner_map_map (crossVec v w) p,
    ← tangentCircleAlign_cross, tangentCircleAlign_pole p hp,
    real_inner_comm circleNorth, circleNorth_inner]
  rfl

/-- Exact additivity of the smaller angles when three unit tangent rays
occur in this order within one open semicircle. -/
theorem tangent_angle_add (p a b d : ℝ³) (hp : ‖p‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0) (hpd : inner ℝ p d = 0)
    (hab : 0 < inner ℝ (crossVec a b) p)
    (hbd : 0 < inner ℝ (crossVec b d) p)
    (had : 0 < inner ℝ (crossVec a d) p) :
    sphereAngle a b + sphereAngle b d = sphereAngle a d := by
  let A := tangentCircleAlign p a
  let B := tangentCircleAlign p b
  let D := tangentCircleAlign p d
  have hA : A 0 ^ 2 + A 1 ^ 2 = 1 := tangentCircleAlign_planar_unit p a hp ha hpa
  have hB : B 0 ^ 2 + B 1 ^ 2 = 1 := tangentCircleAlign_planar_unit p b hp hb hpb
  have hD : D 0 ^ 2 + D 1 ^ 2 = 1 := tangentCircleAlign_planar_unit p d hp hd hpd
  have hab' : 0 < A 0 * B 1 - A 1 * B 0 := by
    simpa only [tangent_triple_coordinates p a b hp] using hab
  have had' : 0 < A 0 * D 1 - A 1 * D 0 := by
    simpa only [tangent_triple_coordinates p a d hp] using had
  have hbd' : 0 < B 0 * D 1 - B 1 * D 0 := by
    simpa only [tangent_triple_coordinates p b d hp] using hbd
  have hrot := planar_rotation_det (A 0) (A 1) (B 0) (B 1) (D 0) (D 1) hA
  have hadd := upper_circle_angle_add
    (A 0 * B 0 + A 1 * B 1) (A 0 * B 1 - A 1 * B 0)
    (A 0 * D 0 + A 1 * D 1) (A 0 * D 1 - A 1 * D 0)
    (planar_rotation_unit _ _ _ _ hA hB) (planar_rotation_unit _ _ _ _ hA hD)
    hab' had' (by rw [hrot]; exact hbd')
  rw [planar_rotation_dot _ _ _ _ _ _ hA] at hadd
  simpa only [sphereAngle, tangent_inner_coordinates p a b hp hpa hpb,
    tangent_inner_coordinates p b d hp hpb hpd, tangent_inner_coordinates p a d hp hpa hpd] using hadd

lemma sphereTangent_triple (p q r : ℝ³) :
    inner ℝ (crossVec (sphereTangent p q) (sphereTangent p r)) p =
      ‖crossVec p r‖⁻¹ * (‖crossVec p q‖⁻¹ * inner ℝ (crossVec q r) p) := by
  simp only [sphereTangent, crossVec_smul_left, crossVec_smul_right,
    inner_smul_left, starRingEnd_apply, star_trivial, cross_projection_triple]

lemma sphereTangent_triple_pos (p q r : ℝ³)
    (htriple : 0 < inner ℝ (crossVec p q) r) :
    0 < inner ℝ (crossVec (sphereTangent p q) (sphereTangent p r)) p := by
  obtain ⟨hpq, _, hrp⟩ := triple_nonzero_cross p q r htriple.ne'
  have hpr : crossVec p r ≠ 0 := by
    intro h
    apply hrp
    rw [crossVec_swap, h, neg_zero]
  rw [sphereTangent_triple]
  apply mul_pos (inv_pos.mpr (norm_pos_iff.mpr hpr))
  apply mul_pos (inv_pos.mpr (norm_pos_iff.mpr hpq))
  rwa [← triple_cyclic]

/-- Splitting a spherical corner by a ray strictly between its two
boundary rays adds the actual, smaller vertex angles. -/
theorem sphereVertexAngle_add (p a b d : ℝ³)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hab : 0 < inner ℝ (crossVec p a) b)
    (hbd : 0 < inner ℝ (crossVec p b) d)
    (had : 0 < inner ℝ (crossVec p a) d) :
    sphereVertexAngle p a b + sphereVertexAngle p b d = sphereVertexAngle p a d := by
  have hpa := (triple_nonzero_cross p a b hab.ne').1
  have hpb := (triple_nonzero_cross p b d hbd.ne').1
  have hpd : crossVec p d ≠ 0 := by
    intro h
    have hdp := (triple_nonzero_cross p a d had.ne').2.2
    apply hdp
    rw [crossVec_swap, h, neg_zero]
  exact tangent_angle_add p _ _ _ hp
    (sphereTangent_unit p a hp ha hpa) (sphereTangent_unit p b hp hb hpb)
    (sphereTangent_unit p d hp hd hpd)
    (sphereTangent_perp p a hp) (sphereTangent_perp p b hp) (sphereTangent_perp p d hp)
    (sphereTangent_triple_pos p a b hab) (sphereTangent_triple_pos p b d hbd)
    (sphereTangent_triple_pos p a d had)

end SquareAntiprismVerification
