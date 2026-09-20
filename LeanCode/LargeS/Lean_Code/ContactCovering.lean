import Lean_Code.ContactGeometryGlobal

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma inner_normalized (v x : ℝ³) :
    inner ℝ (‖v‖⁻¹ • v) x = inner ℝ v x / ‖v‖ := by
  simp [inner_smul_left, div_eq_mul_inv, mul_comm]

/-- Scalar covering argument for a contact triangle, written on its
normalized positive cone. -/
theorem contact_triangle_covering (a b d : ℝ³) (c l μ ν : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hc : 0 < c) (hcupper : c < 1)
    (hab : inner ℝ a b = c) (had : inner ℝ a d = c) (hbd : inner ℝ b d = c)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hsum : l + μ + ν = 1) :
    let z := ‖l • a + μ • b + ν • d‖⁻¹ • (l • a + μ • b + ν • d)
    c < inner ℝ z a ∨ c < inner ℝ z b ∨ c < inner ℝ z d := by
  let v := l • a + μ • b + ν • d
  have hba : inner ℝ b a = c := by rw [real_inner_comm]; exact hab
  have hda : inner ℝ d a = c := by rw [real_inner_comm]; exact had
  have hdb : inner ℝ d b = c := by rw [real_inner_comm]; exact hbd
  have hnormsq : ‖v‖ ^ 2 = c + (1 - c) * (l ^ 2 + μ ^ 2 + ν ^ 2) := by
    dsimp [v]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [hab, had, hbd, hba, hda, hdb]
    simp only [real_inner_self_eq_norm_sq, ha, hb, hd, one_pow]
    nlinarith [congrArg (fun x : ℝ => c * x ^ 2) hsum]
  have hnormlower : c ≤ ‖v‖ ^ 2 := by
    have := mul_nonneg (by linarith : 0 ≤ 1 - c) (by positivity : 0 ≤ l ^ 2 + μ ^ 2 + ν ^ 2)
    linarith
  have hnorm : c < ‖v‖ := by
    have hcc := mul_pos hc (by linarith : 0 < 1 - c)
    nlinarith [norm_nonneg v]
  have hvpos : 0 < ‖v‖ := hc.trans hnorm
  change c < inner ℝ (‖v‖⁻¹ • v) a ∨ c < inner ℝ (‖v‖⁻¹ • v) b ∨ c < inner ℝ (‖v‖⁻¹ • v) d
  by_contra hn
  push_neg at hn
  obtain ⟨hza, hzb, hzd⟩ := hn
  rw [inner_normalized] at hza hzb hzd
  have ha' := (div_le_iff₀ hvpos).mp hza
  have hb' := (div_le_iff₀ hvpos).mp hzb
  have hd' := (div_le_iff₀ hvpos).mp hzd
  have h₁ := mul_le_mul_of_nonneg_left ha' hl
  have h₂ := mul_le_mul_of_nonneg_left hb' hμ
  have h₃ := mul_le_mul_of_nonneg_left hd' hν
  have hself : l * inner ℝ v a + μ * inner ℝ v b + ν * inner ℝ v d = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    conv_rhs => rhs; unfold v
    simp [inner_add_right, inner_smul_right]
  have hbound : ‖v‖ ^ 2 ≤ c * ‖v‖ := by
    have heq : (l + μ + ν) * (c * ‖v‖) = c * ‖v‖ := by rw [hsum, one_mul]
    nlinarith
  nlinarith [mul_pos hvpos (sub_pos.mpr hnorm)]

lemma two_point_combination_norm_sq (a d : ℝ³) (l ν : ℝ)
    (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) :
    ‖l • a + ν • d‖ ^ 2 = l ^ 2 + ν ^ 2 + 2 * l * ν * inner ℝ a d := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [real_inner_comm d a]
  simp only [real_inner_self_eq_norm_sq, ha, hd, one_pow]
  ring

lemma short_diagonal_combination_norm (a d : ℝ³) (c l ν : ℝ)
    (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) (hc : 0 < c)
    (hdiag : 2 * c ^ 2 - 1 < inner ℝ a d) (hbase : 0 < l + ν) :
    c * (l + ν) < ‖l • a + ν • d‖ := by
  have hupper : inner ℝ a d ≤ 1 := by simpa [ha, hd] using real_inner_le_norm a d
  have h₁ := mul_pos (by linarith : 0 < (1 + inner ℝ a d) / 2 - c ^ 2)
    (sq_pos_of_pos hbase)
  have h₂ := mul_nonneg (by linarith : 0 ≤ (1 - inner ℝ a d) / 2) (sq_nonneg (l - ν))
  have hs := two_point_combination_norm_sq a d l ν ha hd
  have hn := norm_nonneg (l • a + ν • d)
  nlinarith [mul_pos hc hbase]

/-- Covering either triangle of a contact rhombus by the balls at the
opposite diagonal endpoints.  Positive total base weight excludes the apex. -/
theorem contact_rhombus_triangle_covering (a b d : ℝ³) (c l μ ν : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (hc : 0 < c)
    (hab : inner ℝ a b = c) (hdb : inner ℝ d b = c)
    (hdiag : 2 * c ^ 2 - 1 < inner ℝ a d)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hbase : 0 < l + ν) :
    let z := ‖l • a + ν • d + μ • b‖⁻¹ • (l • a + ν • d + μ • b)
    c < inner ℝ z a ∨ c < inner ℝ z d := by
  let w := l • a + ν • d
  let v := w + μ • b
  have hwlower : c * (l + ν) < ‖w‖ := short_diagonal_combination_norm a d c l ν ha hd hc hdiag hbase
  have hwpos : 0 < ‖w‖ := (mul_pos hc hbase).trans hwlower
  have hwb : inner ℝ w b = c * (l + ν) := by
    dsimp [w]
    simp [inner_add_left, inner_smul_left, hab, hdb]
    ring
  have hvb : inner ℝ v b = c * (l + ν) + μ := by
    dsimp [v]
    simp [inner_add_left, inner_smul_left, hwb, hb]
  have hbw : inner ℝ b w = c * (l + ν) := (real_inner_comm w b).trans hwb
  have hvpos : 0 < ‖v‖ := by
    have h := real_inner_le_norm v b
    rw [hvb, hb, mul_one] at h
    nlinarith [mul_pos hc hbase]
  have hvupper : ‖v‖ ≤ ‖w‖ + μ := by
    have h := norm_add_le w (μ • b)
    simpa [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ, hb] using h
  change c < inner ℝ (‖v‖⁻¹ • v) a ∨ c < inner ℝ (‖v‖⁻¹ • v) d
  by_contra hn
  push_neg at hn
  obtain ⟨hza, hzd⟩ := hn
  rw [inner_normalized] at hza hzd
  have ha' := (div_le_iff₀ hvpos).mp hza
  have hd' := (div_le_iff₀ hvpos).mp hzd
  have h₁ := mul_le_mul_of_nonneg_left ha' hl
  have h₂ := mul_le_mul_of_nonneg_left hd' hν
  have hvw : inner ℝ v w = ‖w‖ ^ 2 + μ * c * (l + ν) := by
    dsimp [v]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
    rw [real_inner_self_eq_norm_sq, hbw]
    ring
  have hvw' : inner ℝ v w = l * inner ℝ v a + ν * inner ℝ v d := by
    dsimp [w]
    simp [inner_add_right, inner_smul_right]
  have hbound := mul_le_mul_of_nonneg_left hvupper (mul_nonneg hc.le hbase.le)
  nlinarith [mul_pos hwpos (sub_pos.mpr hwlower)]

end SquareAntiprismVerification
