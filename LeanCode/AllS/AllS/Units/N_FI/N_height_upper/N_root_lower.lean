import Blueprint.FiniteDefinitions

noncomputable section
namespace Blueprint.Thomson.Finite

theorem height_upper_root_lower (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (ha1 : a < 1) (hF : F s a = 0) : aInf < a := by
  change SquareAntiprismVerification.aInf < a
  change SquareAntiprismVerification.F s a = 0 at hF
  by_contra h
  have hle : a ≤ SquareAntiprismVerification.aInf := le_of_not_gt h
  have hmem := SquareAntiprismVerification.aInf_mem_Ioo
  have hmono := (SquareAntiprismVerification.F_strictMonoOn s hs).monotoneOn
    (show a ∈ Set.Ico (0 : ℝ) 1 from ⟨ha.le, ha1⟩)
    (show SquareAntiprismVerification.aInf ∈ Set.Ico (0 : ℝ) 1 from ⟨hmem.1.le, hmem.2⟩) hle
  have hneg := SquareAntiprismVerification.F_aInf_neg s hs
  linarith

#check height_upper_root_lower
#print axioms height_upper_root_lower
end Blueprint.Thomson.Finite
