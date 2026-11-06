import Blueprint.FiniteDefinitions

/-! A complete representative analytic leaf, including the logarithmic branch.
Higher jets, Rolle/Hermite and the full finite theorem remain separate work. -/
noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem hasDerivAt_phi (s t : ℝ) (_hs : 0 ≤ s) (ht : t < 1) :
    HasDerivAt (phi s) ((2 - 2 * t) ^ (-1 - s / 2)) t := by
  have hdpos : 0 < 2 - 2 * t := by linarith
  have hd : HasDerivAt (fun x : ℝ => 2 - 2 * x) (-2) t := by
    convert! (hasDerivAt_const t (2 : ℝ)).sub ((hasDerivAt_id t).const_mul 2) using 1 <;> norm_num
  by_cases hs : s = 0
  · subst s
    have h := (hd.log (ne_of_gt hdpos)).const_mul (-(1 / 2 : ℝ))
    convert! h using 1
    · ext x
      simp [phi]
    · simp only [zero_div, sub_zero, Real.rpow_neg_one]
      ring
  · have h := ((hd.rpow_const (p := -s / 2) (Or.inl (ne_of_gt hdpos))).sub_const 1).div_const s
    convert! h using 1
    · ext x
      simp [phi, hs]
    · have he : -s / 2 - 1 = -1 - s / 2 := by ring
      rw [he]
      field_simp [hs]

#print axioms hasDerivAt_phi
end Blueprint.Thomson.Finite
