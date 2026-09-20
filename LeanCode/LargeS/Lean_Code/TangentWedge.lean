import Lean_Code.TangentAngles

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma tangent_triple_circle (p a b : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0) :
    inner ℝ a b ^ 2 + inner ℝ (crossVec a b) p ^ 2 = 1 := by
  rw [tangent_inner_coordinates p a b hp hpa hpb, tangent_triple_coordinates p a b hp]
  exact planar_rotation_unit _ _ _ _
    (tangentCircleAlign_planar_unit p a hp ha hpa) (tangentCircleAlign_planar_unit p b hp hb hpb)

lemma tangent_angle_sin (p a b : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0)
    (hab : 0 < inner ℝ (crossVec a b) p) :
    Real.sin (sphereAngle a b) = inner ℝ (crossVec a b) p := by
  have h := circlePhase_sin (inner ℝ a b) (inner ℝ (crossVec a b) p)
    (tangent_triple_circle p a b hp ha hb hpa hpb)
  simpa only [circlePhase, if_pos hab.le, sphereAngle] using h

lemma tangent_angle_mem_Ioo (p a b : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0)
    (hab : 0 < inner ℝ (crossVec a b) p) : sphereAngle a b ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hcircle := tangent_triple_circle p a b hp ha hb hpa hpb
  have hsq := sq_pos_of_pos hab
  have hlow : -1 < inner ℝ a b := by nlinarith
  have hhigh : inner ℝ a b < 1 := by nlinarith
  exact ⟨Real.arccos_pos.mpr hhigh, Real.arccos_lt_pi.mpr hlow⟩

lemma tangent_triple_difference (p a b d : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0) (hpd : inner ℝ p d = 0) :
    inner ℝ a b * inner ℝ (crossVec a d) p - inner ℝ (crossVec a b) p * inner ℝ a d =
      inner ℝ (crossVec b d) p := by
  rw [tangent_inner_coordinates p a b hp hpa hpb, tangent_inner_coordinates p a d hp hpa hpd,
    tangent_triple_coordinates p a d hp, tangent_triple_coordinates p a b hp,
    tangent_triple_coordinates p b d hp]
  exact planar_rotation_det _ _ _ _ _ _ (tangentCircleAlign_planar_unit p a hp ha hpa)

theorem tangent_triple_pos_of_angle_lt (p a b d : ℝ³) (hp : ‖p‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hpa : inner ℝ p a = 0) (hpb : inner ℝ p b = 0) (hpd : inner ℝ p d = 0)
    (hab : 0 < inner ℝ (crossVec a b) p) (had : 0 < inner ℝ (crossVec a d) p)
    (hlt : sphereAngle a b < sphereAngle a d) : 0 < inner ℝ (crossVec b d) p := by
  have hdiff : inner ℝ (crossVec b d) p = Real.sin (sphereAngle a d - sphereAngle a b) := by
    rw [Real.sin_sub, tangent_angle_sin p a d hp ha hd hpa hpd had,
      tangent_angle_sin p a b hp ha hb hpa hpb hab,
      cos_sphereAngle a b ha hb, cos_sphereAngle a d ha hd]
    have h := tangent_triple_difference p a b d hp ha hpa hpb hpd
    nlinarith
  rw [hdiff]
  apply Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt)
  have habrange := tangent_angle_mem_Ioo p a b hp ha hb hpa hpb hab
  linarith [habrange.1, (sphereAngle_range a d).2]

lemma sphereVertexAngle_pos (p a b : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : 0 < inner ℝ (crossVec p a) b) : 0 < sphereVertexAngle p a b := by
  obtain ⟨hpa, _, hbp⟩ := triple_nonzero_cross p a b hab.ne'
  have hpb : crossVec p b ≠ 0 := by
    intro h
    apply hbp
    rw [crossVec_swap, h, neg_zero]
  exact (tangent_angle_mem_Ioo p _ _ hp
    (sphereTangent_unit p a hp ha hpa) (sphereTangent_unit p b hp hb hpb)
    (sphereTangent_perp p a hp) (sphereTangent_perp p b hp)
    (sphereTangent_triple_pos p a b hab)).1

theorem sphere_triple_pos_of_vertexAngle_lt (p a b d : ℝ³)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hab : 0 < inner ℝ (crossVec p a) b) (had : 0 < inner ℝ (crossVec p a) d)
    (hlt : sphereVertexAngle p a b < sphereVertexAngle p a d) :
    0 < inner ℝ (crossVec p b) d := by
  have hpa := (triple_nonzero_cross p a b hab.ne').1
  have hpb : crossVec p b ≠ 0 := by
    intro h
    have hbp := (triple_nonzero_cross p a b hab.ne').2.2
    apply hbp
    rw [crossVec_swap, h, neg_zero]
  have hpd : crossVec p d ≠ 0 := by
    intro h
    have hdp := (triple_nonzero_cross p a d had.ne').2.2
    apply hdp
    rw [crossVec_swap, h, neg_zero]
  have ht := tangent_triple_pos_of_angle_lt p _ _ _ hp
    (sphereTangent_unit p a hp ha hpa) (sphereTangent_unit p b hp hb hpb)
    (sphereTangent_unit p d hp hd hpd)
    (sphereTangent_perp p a hp) (sphereTangent_perp p b hp) (sphereTangent_perp p d hp)
    (sphereTangent_triple_pos p a b hab) (sphereTangent_triple_pos p a d had) hlt
  rw [sphereTangent_triple, ← triple_cyclic] at ht
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (crossVec p d)))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (crossVec p b))) (le_of_not_gt h))
  linarith

end SquareAntiprismVerification
