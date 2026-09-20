import Lean_Code.CrossAlgebra
import Lean_Code.ContactCovering

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Cramer's rule in vector form, with the orientation made explicit. -/
lemma triple_cramer (a b d z : ℝ³) :
    inner ℝ (crossVec a b) d • z =
      inner ℝ (crossVec b d) z • a +
        inner ℝ (crossVec d a) z • b + inner ℝ (crossVec a b) z • d := by
  ext i
  fin_cases i <;> simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ] <;> ring

/-- Three oriented edge halfspaces give nonnegative cone coordinates. -/
theorem spherical_triangle_cone (a b d z : ℝ³)
    (horient : 0 < inner ℝ (crossVec a b) d)
    (hab : 0 ≤ inner ℝ (crossVec a b) z)
    (hbd : 0 ≤ inner ℝ (crossVec b d) z)
    (hda : 0 ≤ inner ℝ (crossVec d a) z) :
    ∃ l μ ν : ℝ, 0 ≤ l ∧ 0 ≤ μ ∧ 0 ≤ ν ∧ z = l • a + μ • b + ν • d := by
  let t := inner ℝ (crossVec a b) d
  refine ⟨inner ℝ (crossVec b d) z / t, inner ℝ (crossVec d a) z / t,
    inner ℝ (crossVec a b) z / t, div_nonneg hbd horient.le,
    div_nonneg hda horient.le, div_nonneg hab horient.le, ?_⟩
  have h := congrArg (fun v : ℝ³ => t⁻¹ • v) (triple_cramer a b d z)
  simpa [t, smul_add, smul_smul, horient.ne', div_eq_mul_inv, mul_comm] using h

lemma contact_triangle_cone_covering (a b d z : ℝ³) (c l μ ν : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hz : ‖z‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (had : inner ℝ a d = c) (hbd : inner ℝ b d = c)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hrep : z = l • a + μ • b + ν • d) :
    c < inner ℝ z a ∨ c < inner ℝ z b ∨ c < inner ℝ z d := by
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hda : inner ℝ d a = c := (real_inner_comm a d).trans had
  have hdb : inner ℝ d b = c := (real_inner_comm b d).trans hbd
  have hsq : 1 = c * (l + μ + ν) ^ 2 + (1 - c) * (l ^ 2 + μ ^ 2 + ν ^ 2) := by
    have hs : inner ℝ z z = 1 := by simp [hz]
    rw [hrep] at hs
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq,
      ha, hb, hd, hab, had, hbd, hba, hda, hdb, one_pow] at hs
    nlinarith [hs]
  have hweight : l * inner ℝ z a + μ * inner ℝ z b + ν * inner ℝ z d = 1 := by
    calc
      _ = inner ℝ z (l • a + μ • b + ν • d) := by simp [inner_add_right, inner_smul_right]
      _ = 1 := by rw [← hrep]; simp [hz]
  by_contra hnot
  push_neg at hnot
  obtain ⟨hza, hzb, hzd⟩ := hnot
  have hw : 1 ≤ c * (l + μ + ν) := by
    nlinarith [mul_le_mul_of_nonneg_left hza hl, mul_le_mul_of_nonneg_left hzb hμ,
      mul_le_mul_of_nonneg_left hzd hν]
  have hs : c * (l + μ + ν) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le)
      (show 0 ≤ l ^ 2 + μ ^ 2 + ν ^ 2 by positivity)]
  have ht : l + μ + ν ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hw (show 0 ≤ l + μ + ν by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left ht hc.1.le, hc.2]

/-- The covering estimate now applies directly to the closed geometric
triangle, represented by its three edge halfspaces. -/
theorem contact_triangle_halfspace_covering (a b d z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hz : ‖z‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (had : inner ℝ a d = c) (hbd : inner ℝ b d = c)
    (horient : 0 < inner ℝ (crossVec a b) d)
    (hleftab : 0 ≤ inner ℝ (crossVec a b) z)
    (hleftbd : 0 ≤ inner ℝ (crossVec b d) z)
    (hleftda : 0 ≤ inner ℝ (crossVec d a) z) :
    c < inner ℝ z a ∨ c < inner ℝ z b ∨ c < inner ℝ z d := by
  obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := spherical_triangle_cone a b d z horient
    hleftab hleftbd hleftda
  exact contact_triangle_cone_covering a b d z c l μ ν ha hb hd hz hc hab had hbd hl hμ hν hrep

lemma contact_diagonal_short (a b d : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c)
    (horient : inner ℝ (crossVec a b) d ≠ 0) :
    2 * c ^ 2 - 1 < inner ℝ a d := by
  have hs := sphereAngle_cos_add_strict a b d ha hb hd horient
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    have h := abs_real_inner_le_norm a b
    rw [ha, hb, hab, one_mul] at h
    exact abs_le.mp h
  have hsin := Real.sin_sq_add_cos_sq (Real.arccos c)
  rw [Real.cos_arccos hc.1 hc.2] at hsin
  simp only [sphereAngle, hab, hbd, Real.cos_add, Real.cos_arccos hc.1 hc.2,
    ← pow_two] at hs
  nlinarith [hsin]

lemma contact_rhombus_cone_covering (a b d z : ℝ³) (c l μ ν : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hz : ‖z‖ = 1)
    (hc : 0 < c) (hab : inner ℝ a b = c) (hdb : inner ℝ d b = c)
    (hdiag : 2 * c ^ 2 - 1 < inner ℝ a d)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hrep : z = l • a + μ • b + ν • d) (hne : z ≠ b) :
    c < inner ℝ z a ∨ c < inner ℝ z d := by
  have hbase : 0 < l + ν := by
    by_contra hn
    have hl0 : l = 0 := by linarith
    have hν0 : ν = 0 := by linarith
    have hrep' : z = μ • b := by simpa [hl0, hν0] using hrep
    have hμ1 : μ = 1 := by
      have hn := congrArg norm hrep'
      simpa [hz, hb, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] using hn.symm
    exact hne (by simpa [hμ1] using hrep')
  have h := contact_rhombus_triangle_covering a b d c l μ ν ha hb hd hc hab hdb hdiag
    hl hμ hν hbase
  have hrep' : l • a + ν • d + μ • b = z := by rw [hrep]; module
  simpa only [hrep', hz, inv_one, one_smul] using h

/-- Split the closed rhombus along its diagonal, using only determinant
signs. Away from the two apices, one diagonal endpoint is strictly closer
than the contact distance. -/
theorem contact_rhombus_halfspace_covering (a b d e z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1) (hz : ‖z‖ = 1)
    (hc : 0 < c)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c)
    (hde : inner ℝ d e = c) (hea : inner ℝ e a = c)
    (horient₁ : 0 < inner ℝ (crossVec a b) d)
    (horient₂ : 0 < inner ℝ (crossVec a d) e)
    (hleftab : 0 ≤ inner ℝ (crossVec a b) z)
    (hleftbd : 0 ≤ inner ℝ (crossVec b d) z)
    (hleftde : 0 ≤ inner ℝ (crossVec d e) z)
    (hleftea : 0 ≤ inner ℝ (crossVec e a) z)
    (hneb : z ≠ b) (hnee : z ≠ e) :
    c < inner ℝ z a ∨ c < inner ℝ z d := by
  have hdiag := contact_diagonal_short a b d c ha hb hd hab hbd horient₁.ne'
  by_cases hside : 0 ≤ inner ℝ (crossVec a d) z
  · obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := spherical_triangle_cone a d e z horient₂
      hside hleftde hleftea
    have hrep' : z = l • a + ν • e + μ • d := by rw [hrep]; module
    exact contact_rhombus_cone_covering a e d z c l ν μ ha he hd hz hc
      ((real_inner_comm e a).trans hea) hde hdiag hl hν hμ hrep' hnee
  · have hleftda : 0 ≤ inner ℝ (crossVec d a) z := by
      have hswap : crossVec d a = -crossVec a d := by
        ext i
        fin_cases i <;> simp [crossVec] <;> ring
      rw [hswap, inner_neg_left]
      linarith
    obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := spherical_triangle_cone a b d z horient₁
      hleftab hleftbd hleftda
    exact contact_rhombus_cone_covering a b d z c l μ ν ha hb hd hz hc hab
      ((real_inner_comm b d).trans hbd) hdiag hl hμ hν hrep hneb

end SquareAntiprismVerification
