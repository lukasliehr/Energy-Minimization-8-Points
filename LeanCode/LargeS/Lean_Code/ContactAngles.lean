import Lean_Code.ContactDirections
import Lean_Code.RhombusScalar
import Lean_Code.SphericalTriangle

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def contactAngle (c : ℝ) (q r : ℝ³) : ℝ :=
  Real.arccos ((inner ℝ q r - c ^ 2) / (1 - c ^ 2))

lemma contact_tangent_inner (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    inner ℝ (q - c • p) (r - c • p) = inner ℝ q r - c ^ 2 := by
  have hqp : inner ℝ q p = c := (real_inner_comm p q).trans hpq
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [hqp, hpr]
  simp only [real_inner_self_eq_norm_sq, hp, one_pow]
  ring

lemma contact_cosine_ratio_range (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    (inner ℝ q r - c ^ 2) / (1 - c ^ 2) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hq' := (contact_tangent_norm_sq p q c hp hq hpq).2
  have hr' := (contact_tangent_norm_sq p r c hp hr hpr).2
  have hnorm : ‖q - c • p‖ = ‖r - c • p‖ := by
    nlinarith [norm_nonneg (q - c • p), norm_nonneg (r - c • p)]
  have hbound := abs_real_inner_le_norm (q - c • p) (r - c • p)
  rw [← hnorm, ← pow_two, hq', contact_tangent_inner p q r c hp hpq hpr] at hbound
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  constructor
  · apply (le_div_iff₀ hden).mpr
    linarith
  · exact (div_le_one hden).mpr hhi

lemma contact_angle_cos (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    Real.cos (contactAngle c q r) = (inner ℝ q r - c ^ 2) / (1 - c ^ 2) := by
  have h := contact_cosine_ratio_range p q r c hp hq hr hc hpq hpr
  exact Real.cos_arccos h.1 h.2

theorem contact_angle_cosine_identity (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    inner ℝ q r = c ^ 2 + (1 - c ^ 2) * Real.cos (contactAngle c q r) := by
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  rw [contact_angle_cos p q r c hp hq hr hc hpq hpr]
  field_simp [hden.ne']
  ring

lemma equilateral_cosine_ratio (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    (c - c ^ 2) / (1 - c ^ 2) = c / (1 + c) := by
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  have hplus : 1 + c ≠ 0 := by linarith [hc.1]
  field_simp [hden.ne', hplus]
  ring

lemma equilateral_contact_angle (q r : ℝ³) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hqr : inner ℝ q r = c) :
    contactAngle c q r = Real.arccos (c / (1 + c)) := by
  rw [contactAngle, hqr, equilateral_cosine_ratio c hc]

theorem contact_angle_lower_bound (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c)
    (hqr : inner ℝ q r ≤ c) : Real.arccos (c / (1 + c)) ≤ contactAngle c q r := by
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  have hratio : (inner ℝ q r - c ^ 2) / (1 - c ^ 2) ≤ c / (1 + c) := by
    rw [← equilateral_cosine_ratio c hc]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hmaxpos : 0 < c / (1 + c) := div_pos hc.1 (by linarith [hc.1])
  have hmaxlt : c / (1 + c) < 1 := (div_lt_one (by linarith [hc.1])).mpr (by linarith)
  by_contra h
  have hlt := Real.strictAntiOn_cos
    (show contactAngle c q r ∈ Set.Icc (0 : ℝ) Real.pi from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
    (show Real.arccos (c / (1 + c)) ∈ Set.Icc (0 : ℝ) Real.pi from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩) (lt_of_not_ge h)
  rw [contact_angle_cos p q r c hp hq hr hc hpq hpr,
    Real.cos_arccos (by linarith : -1 ≤ c / (1 + c)) hmaxlt.le] at hlt
  linarith

theorem angle_sum_at_most_four (n : ℕ) (α : ℝ) (hα : 2 * Real.pi / 5 < α)
    (θ : Fin n → ℝ) (hθ : ∀ i, α ≤ θ i) (hsum : ∑ i, θ i = 2 * Real.pi) : n ≤ 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hθ i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at h
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hn : (n : ℝ) < 5 := by nlinarith
  have hnat : n < 5 := by exact_mod_cast hn
  omega

theorem contact_angle_strict_lower_bound (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c)
    (hqr : inner ℝ q r < c) : Real.arccos (c / (1 + c)) < contactAngle c q r := by
  refine lt_of_le_of_ne (contact_angle_lower_bound p q r c hp hq hr hc hpq hpr hqr.le) ?_
  intro heq
  have hcos := contact_angle_cosine_identity p q r c hp hq hr hc hpq hpr
  rw [← heq] at hcos
  have hratio : c / (1 + c) ∈ Set.Icc (-1 : ℝ) 1 := by
    have hpos := div_pos hc.1 (by linarith [hc.1] : 0 < 1 + c)
    have hlt := (div_lt_one (by linarith [hc.1] : 0 < 1 + c)).mpr (by linarith : c < 1 + c)
    exact ⟨by linarith, hlt.le⟩
  rw [Real.cos_arccos hratio.1 hratio.2] at hcos
  have hidentity : c ^ 2 + (1 - c ^ 2) * (c / (1 + c)) = c := by
    field_simp [ne_of_gt (show 0 < 1 + c by linarith [hc.1])]
    ring
  rw [hidentity] at hcos
  linarith

theorem sphereVertexAngle_eq_contactAngle (p q r : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpq : inner ℝ p q = c) (hpr : inner ℝ p r = c) :
    sphereVertexAngle p q r = contactAngle c q r := by
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  have hnq : ‖crossVec p q‖ ^ 2 = 1 - c ^ 2 := by
    rw [crossVec_norm_sq, hp, hq, hpq]
    ring
  have hnr : ‖crossVec p r‖ ^ 2 = 1 - c ^ 2 := by
    rw [crossVec_norm_sq, hp, hr, hpr]
    ring
  have hnorms : ‖crossVec p r‖ = ‖crossVec p q‖ := by
    nlinarith [norm_nonneg (crossVec p q), norm_nonneg (crossVec p r)]
  have hnonzero : ‖crossVec p q‖ ≠ 0 := by intro h; rw [h] at hnq; nlinarith
  unfold sphereVertexAngle sphereAngle contactAngle sphereTangent
  congr 1
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, hpq, hpr,
    contact_tangent_inner p q r c hp hpq hpr, hnorms]
  field_simp [hnonzero, hden.ne']
  rw [hnq]
  ring

end SquareAntiprismVerification
