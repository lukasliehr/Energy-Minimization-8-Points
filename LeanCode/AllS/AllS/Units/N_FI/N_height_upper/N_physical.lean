import AllS.Units.N_FI.N_height_upper.N_root_lower
import AllS.Units.N_FI.N_height_upper.N_third_positive

noncomputable section
namespace Blueprint.Thomson.Finite

theorem height_upper_physical (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (ha1 : a < 1) (hF : F s a = 0) : physical a := by
  refine ⟨height_upper_root_lower s a hs ha ha1 hF, ?_⟩
  by_contra h
  have hle : (1/3 : ℝ) ≤ a := le_of_not_gt h
  have hpos := height_upper_third_positive s hs
  change SquareAntiprismVerification.F s (1/3) > 0 at hpos
  change SquareAntiprismVerification.F s a = 0 at hF
  have hmono := (SquareAntiprismVerification.F_strictMonoOn s hs).monotoneOn
    (show (1/3 : ℝ) ∈ Set.Ico (0 : ℝ) 1 by norm_num)
    (show a ∈ Set.Ico (0 : ℝ) 1 from ⟨ha.le,ha1⟩) hle
  linarith

#check height_upper_physical
#print axioms height_upper_physical
end Blueprint.Thomson.Finite
