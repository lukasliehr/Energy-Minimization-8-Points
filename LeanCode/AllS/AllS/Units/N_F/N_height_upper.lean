import AllS.Units.N_FI.N_height_upper.N_physical
import AllS.Units.N_F.N_definitions

noncomputable section
namespace Blueprint.Thomson.Finite

theorem stationary_height_upper (s a : ℝ) (hs : 0 ≤ s) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F s a = 0) : physical a :=
  height_upper_physical s a hs ha.1 ha.2 hF

theorem aS_physical (s : ℝ) (hs : 0 ≤ s) : physical (aS s) := by
  obtain ⟨ha,hF⟩ := aS_mem_and_root s hs
  exact height_upper_physical s (aS s) hs ha.1 ha.2 hF

#check stationary_height_upper
#print axioms stationary_height_upper
#print axioms aS_physical
end Blueprint.Thomson.Finite
