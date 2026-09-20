import Lean_Code.ContactCertificate

open Real
noncomputable section
namespace SquareAntiprismVerification

def stressWeight : ℝ := 1 + 1 / √2

/-- Paper Lemma 5.3 in infinitesimal azimuth/height coordinates: square
contacts have weight `1 + 1/√2`, cross contacts have weight one, and the
weighted contact differential vanishes identically. -/
theorem exact_positive_stress (α β : Fin 8 → ℝ) :
    stressWeight *
        (rigidityRow 0 1 α β + rigidityRow 1 2 α β +
          rigidityRow 2 3 α β + rigidityRow 3 0 α β +
          rigidityRow 4 5 α β + rigidityRow 5 6 α β +
          rigidityRow 6 7 α β + rigidityRow 7 4 α β) +
      (rigidityRow 0 4 α β + rigidityRow 0 7 α β +
        rigidityRow 1 4 α β + rigidityRow 1 5 α β +
        rigidityRow 2 5 α β + rigidityRow 2 6 α β +
        rigidityRow 3 6 α β + rigidityRow 3 7 α β) = 0 := by
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2ne : √(2 : ℝ) ≠ 0 := ne_of_gt sqrt_two_pos
  have hs2cube : √(2 : ℝ) ^ 3 = 2 * √2 := by
    calc
      √(2 : ℝ) ^ 3 = √2 ^ 2 * √2 := by ring
      _ = 2 * √2 := by rw [hs2]
  have hs3s : sin (3 * π / 4) = √2 / 2 := by
    rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.sin_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs3c : cos (3 * π / 4) = -√2 / 2 := by
    rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.cos_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs5s : sin (5 * π / 4) = -√2 / 2 := by
    rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.sin_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs5c : cos (5 * π / 4) = -√2 / 2 := by
    rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.cos_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs7s : sin (7 * π / 4) = -√2 / 2 := by
    rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.sin_sub]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs7c : cos (7 * π / 4) = √2 / 2 := by
    rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.cos_sub]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs32s : sin (3 * π / 2) = -1 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.sin_add]
    simp
  have hs32c : cos (3 * π / 2) = 0 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.cos_add]
    simp
  simp only [stressWeight, rigidityRow, aInf, Real.sin_sub, Real.cos_sub,
    azimuth_0, azimuth_1, azimuth_2, azimuth_3, azimuth_4, azimuth_5,
    azimuth_6, azimuth_7, layerSign_0, layerSign_1, layerSign_2, layerSign_3,
    layerSign_4, layerSign_5, layerSign_6, layerSign_7]
  norm_num [Real.sin_pi_div_four, Real.cos_pi_div_four, hs3s, hs3c, hs5s,
    hs5c, hs7s, hs7c, hs32s, hs32c]
  field_simp [hs2ne]
  all_goals ring_nf
  all_goals simp only [hs2, hs2cube]
  all_goals ring

end SquareAntiprismVerification
