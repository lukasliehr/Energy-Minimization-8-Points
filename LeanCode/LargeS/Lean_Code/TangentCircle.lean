import Lean_Code.CirclePhase
import Lean_Code.ContactAngles
import Lean_Code.CrossRotations

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def circleNorth : ℝ³ := !₂[0, 0, 1]

lemma circleNorth_norm : ‖circleNorth‖ = 1 := by
  have h : ‖circleNorth‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_coordinate_sum]
    norm_num [circleNorth, Fin.sum_univ_succ]
  nlinarith [norm_nonneg circleNorth]

lemma circleNorth_inner (x : ℝ³) : inner ℝ circleNorth x = x 2 := by
  simp [circleNorth, inner_coordinate_sum, Fin.sum_univ_succ]

def circleEast : ℝ³ := !₂[1, 0, 0]

lemma circleEast_ne_zero : circleEast ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : ℝ³ => v 0) h
  norm_num [circleEast] at h0

/-- An orientation-preserving pole alignment. At the antipodal pole use
a genuine half-turn, avoiding the degenerate zero-axis reflection. -/
def tangentCircleAlign (p : ℝ³) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  if p + circleNorth = 0 then lineReflection circleEast else alignVector p circleNorth

lemma tangentCircleAlign_pole (p : ℝ³) (hp : ‖p‖ = 1) :
    tangentCircleAlign p p = circleNorth := by
  unfold tangentCircleAlign
  split_ifs with h
  · have hpneg : p = -circleNorth := eq_neg_of_add_eq_zero_left h
    rw [hpneg, lineReflection_orthogonal circleEast (-circleNorth)]
    · exact neg_neg circleNorth
    · norm_num [circleEast, circleNorth, inner_coordinate_sum, Fin.sum_univ_succ]
  · exact alignVector_maps p circleNorth (hp.trans circleNorth_norm.symm)

theorem tangentCircleAlign_cross (p v w : ℝ³) :
    crossVec (tangentCircleAlign p v) (tangentCircleAlign p w) =
      tangentCircleAlign p (crossVec v w) := by
  unfold tangentCircleAlign
  split_ifs with h
  · exact lineReflection_cross circleEast v w circleEast_ne_zero
  · have hnorth : circleNorth ≠ 0 := norm_ne_zero_iff.mp (by rw [circleNorth_norm]; norm_num)
    simp only [alignVector_apply]
    rw [lineReflection_cross circleNorth _ _ hnorth,
      lineReflection_cross (p + circleNorth) v w h]

lemma tangentCircleAlign_last (p v : ℝ³) (hp : ‖p‖ = 1)
    (htan : inner ℝ p v = 0) : tangentCircleAlign p v 2 = 0 := by
  rw [← circleNorth_inner, ← tangentCircleAlign_pole p hp,
    (tangentCircleAlign p).inner_map_map, htan]

lemma tangentCircleAlign_planar_unit (p v : ℝ³) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (htan : inner ℝ p v = 0) :
    (tangentCircleAlign p v 0) ^ 2 + (tangentCircleAlign p v 1) ^ 2 = 1 := by
  have hnorm := (tangentCircleAlign p).norm_map v
  have hself := real_inner_self_eq_norm_sq (tangentCircleAlign p v)
  rw [hnorm, hv] at hself
  simp only [inner_coordinate_sum, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hself
  change (tangentCircleAlign p v 0) * (tangentCircleAlign p v 0) +
    ((tangentCircleAlign p v 1) * (tangentCircleAlign p v 1) +
      (tangentCircleAlign p v 2) * (tangentCircleAlign p v 2)) = 1 ^ 2 at hself
  rw [tangentCircleAlign_last p v hp htan] at hself
  nlinarith

/-- An angular coordinate on the unit tangent circle at a unit pole. -/
def tangentPhase (p v : ℝ³) : ℝ :=
  circlePhase (tangentCircleAlign p v 0) (tangentCircleAlign p v 1)

lemma tangentPhase_range (p v : ℝ³) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (htan : inner ℝ p v = 0) :
    tangentPhase p v ∈ Set.Ioc (-Real.pi) Real.pi :=
  circlePhase_range _ _ (tangentCircleAlign_planar_unit p v hp hv htan)

theorem tangentPhase_injective (p v w : ℝ³) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hpv : inner ℝ p v = 0) (hpw : inner ℝ p w = 0)
    (heq : tangentPhase p v = tangentPhase p w) : v = w := by
  obtain ⟨hx, hy⟩ := circlePhase_injective _ _ _ _
    (tangentCircleAlign_planar_unit p v hp hv hpv)
    (tangentCircleAlign_planar_unit p w hp hw hpw) heq
  apply (tangentCircleAlign p).injective
  ext i
  fin_cases i
  · exact hx
  · exact hy
  · exact (tangentCircleAlign_last p v hp hpv).trans
      (tangentCircleAlign_last p w hp hpw).symm

theorem tangentPhase_inner (p v w : ℝ³) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hpv : inner ℝ p v = 0) (hpw : inner ℝ p w = 0) :
    inner ℝ v w = Real.cos (tangentPhase p v - tangentPhase p w) := by
  have h := circlePhase_inner _ _ _ _
    (tangentCircleAlign_planar_unit p v hp hv hpv)
    (tangentCircleAlign_planar_unit p w hp hw hpw)
  rw [← (tangentCircleAlign p).inner_map_map v w, inner_coordinate_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change tangentCircleAlign p v 0 * tangentCircleAlign p w 0 +
    (tangentCircleAlign p v 1 * tangentCircleAlign p w 1 +
      tangentCircleAlign p v 2 * tangentCircleAlign p w 2) = _
  rw [tangentCircleAlign_last p v hp hpv, zero_mul, add_zero]
  exact h

theorem tangentPhase_triple (p v w : ℝ³) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hpv : inner ℝ p v = 0) (hpw : inner ℝ p w = 0) :
    inner ℝ (crossVec v w) p = Real.sin (tangentPhase p w - tangentPhase p v) := by
  have huv := tangentCircleAlign_planar_unit p v hp hv hpv
  have huw := tangentCircleAlign_planar_unit p w hp hw hpw
  rw [← (tangentCircleAlign p).inner_map_map (crossVec v w) p,
    ← tangentCircleAlign_cross, tangentCircleAlign_pole p hp,
    real_inner_comm circleNorth, circleNorth_inner]
  simp [crossVec, Real.sin_sub, tangentPhase,
    circlePhase_cos _ _ huv, circlePhase_sin _ _ huv,
    circlePhase_cos _ _ huw, circlePhase_sin _ _ huw, mul_comm]

def tangentAtPhase (p : ℝ³) (θ : ℝ) : ℝ³ :=
  (tangentCircleAlign p).symm !₂[Real.cos θ, Real.sin θ, 0]

lemma tangentAtPhase_unit (p : ℝ³) (θ : ℝ) : ‖tangentAtPhase p θ‖ = 1 := by
  rw [tangentAtPhase, (tangentCircleAlign p).symm.norm_map]
  have h : ‖(!₂[Real.cos θ, Real.sin θ, 0] : ℝ³)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_coordinate_sum]
    simpa [inner_coordinate_sum, Fin.sum_univ_succ, pow_two, add_comm] using
      Real.sin_sq_add_cos_sq θ
  nlinarith [norm_nonneg (!₂[Real.cos θ, Real.sin θ, 0] : ℝ³)]

lemma tangentAtPhase_perp (p : ℝ³) (θ : ℝ) (hp : ‖p‖ = 1) :
    inner ℝ p (tangentAtPhase p θ) = 0 := by
  rw [← (tangentCircleAlign p).inner_map_map p (tangentAtPhase p θ),
    tangentCircleAlign_pole p hp, tangentAtPhase,
    (tangentCircleAlign p).apply_symm_apply, circleNorth_inner]
  rfl

lemma tangentAtPhase_inner (p v : ℝ³) (θ : ℝ) (hp : ‖p‖ = 1)
    (hv : ‖v‖ = 1) (hpv : inner ℝ p v = 0) :
    inner ℝ (tangentAtPhase p θ) v = Real.cos (θ - tangentPhase p v) := by
  have hu := tangentCircleAlign_planar_unit p v hp hv hpv
  rw [← (tangentCircleAlign p).inner_map_map (tangentAtPhase p θ) v,
    tangentAtPhase, (tangentCircleAlign p).apply_symm_apply]
  simp [inner_coordinate_sum, Fin.sum_univ_succ, Real.cos_sub, tangentPhase,
    circlePhase_cos _ _ hu, circlePhase_sin _ _ hu]

lemma sphereTangent_perp (p q : ℝ³) (hp : ‖p‖ = 1) :
    inner ℝ p (sphereTangent p q) = 0 := by
  simp [sphereTangent, inner_smul_right, inner_sub_right, hp]

lemma contact_cross_norm_pos (p q : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : inner ℝ p q = c) : 0 < ‖crossVec p q‖ := by
  have h := crossVec_norm_sq p q
  rw [hp, hq, hcontact] at h
  nlinarith [norm_nonneg (crossVec p q), mul_pos hc.1 (sub_pos.mpr hc.2)]

lemma contact_sphereTangent_unit (p q : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : inner ℝ p q = c) : ‖sphereTangent p q‖ = 1 :=
  sphereTangent_unit p q hp hq
    (norm_pos_iff.mp (contact_cross_norm_pos p q c hp hq hc hcontact))

theorem contact_sphereTangent_injective (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c)
    (heq : sphereTangent p q = sphereTangent p r) : q = r := by
  have hnorm : ‖crossVec p q‖ = ‖crossVec p r‖ := by
    have hq' := crossVec_norm_sq p q
    have hr' := crossVec_norm_sq p r
    rw [hp, hq, hpq] at hq'
    rw [hp, hr, hpr] at hr'
    nlinarith [norm_nonneg (crossVec p q), norm_nonneg (crossVec p r)]
  have hpos := contact_cross_norm_pos p q c hp hq hc hpq
  have h := congrArg (fun v : ℝ³ => ‖crossVec p q‖ • v) heq
  simp only [sphereTangent, ← hnorm, hpq, hpr, smul_smul,
    mul_inv_cancel₀ hpos.ne', one_smul] at h
  exact sub_left_injective h

lemma tangent_contact_inner (p q v : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) (hpv : inner ℝ p v = 0) :
    inner ℝ v q = ‖crossVec p q‖ * inner ℝ v (sphereTangent p q) := by
  have hpos := contact_cross_norm_pos p q c hp hq hc hpq
  have hvp : inner ℝ v p = 0 := (real_inner_comm p v).trans hpv
  simp only [sphereTangent, inner_smul_right, inner_sub_right, hvp, mul_zero, sub_zero]
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

def contactPhase (p q : ℝ³) : ℝ := tangentPhase p (sphereTangent p q)

lemma contactPhase_range (p q : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) : contactPhase p q ∈ Set.Ioc (-Real.pi) Real.pi :=
  tangentPhase_range p _ hp (contact_sphereTangent_unit p q c hp hq hc hpq)
    (sphereTangent_perp p q hp)

theorem contactPhase_injective (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c)
    (heq : contactPhase p q = contactPhase p r) : q = r := by
  apply contact_sphereTangent_injective p q r c hp hq hr hc hpq hpr
  exact tangentPhase_injective p _ _ hp
    (contact_sphereTangent_unit p q c hp hq hc hpq)
    (contact_sphereTangent_unit p r c hp hr hc hpr)
    (sphereTangent_perp p q hp) (sphereTangent_perp p r hp) heq

lemma contactPhase_angle (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    contactAngle c q r = Real.arccos (Real.cos (contactPhase p q - contactPhase p r)) := by
  rw [← sphereVertexAngle_eq_contactAngle p q r c hp hq hr hc hpq hpr]
  unfold sphereVertexAngle sphereAngle
  rw [tangentPhase_inner p _ _ hp
    (contact_sphereTangent_unit p q c hp hq hc hpq)
    (contact_sphereTangent_unit p r c hp hr hc hpr)
    (sphereTangent_perp p q hp) (sphereTangent_perp p r hp)]
  rfl

lemma cross_projection_triple (p q r : ℝ³) (a b : ℝ) :
    inner ℝ (crossVec (q - a • p) (r - b • p)) p = inner ℝ (crossVec q r) p := by
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  ring

theorem contactPhase_triple (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    inner ℝ (crossVec q r) p = ‖crossVec p q‖ * ‖crossVec p r‖ *
      Real.sin (contactPhase p r - contactPhase p q) := by
  have hqpos := contact_cross_norm_pos p q c hp hq hc hpq
  have hrpos := contact_cross_norm_pos p r c hp hr hc hpr
  have ht := tangentPhase_triple p (sphereTangent p q) (sphereTangent p r) hp
    (contact_sphereTangent_unit p q c hp hq hc hpq)
    (contact_sphereTangent_unit p r c hp hr hc hpr)
    (sphereTangent_perp p q hp) (sphereTangent_perp p r hp)
  change inner ℝ (crossVec (sphereTangent p q) (sphereTangent p r)) p =
    Real.sin (contactPhase p r - contactPhase p q) at ht
  simp only [sphereTangent, crossVec_smul_left, crossVec_smul_right,
    inner_smul_left, starRingEnd_apply, star_trivial, cross_projection_triple] at ht
  calc
    inner ℝ (crossVec q r) p = ‖crossVec p q‖ * ‖crossVec p r‖ *
        (‖crossVec p r‖⁻¹ * (‖crossVec p q‖⁻¹ * inner ℝ (crossVec q r) p)) := by
      field_simp [hqpos.ne', hrpos.ne']
    _ = _ := congrArg (fun t : ℝ => ‖crossVec p q‖ * ‖crossVec p r‖ * t) ht

end SquareAntiprismVerification
