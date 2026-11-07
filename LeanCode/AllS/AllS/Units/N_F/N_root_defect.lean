import AllS.Units.N_FI.N_root_defect.N_model_transfer

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem root_defect_enclosure (s P H : ℝ → ℝ) (q₀ C δ e : ℝ)
    (hq₀ : 1 ≤ q₀) (hC : C ≤ rootC)
    (hs : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ s t)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q₀ ≤ 1+s t/2)
    (hP : ∀ t ∈ Set.Icc (-1:ℝ) 1, P t ∈ Set.Icc 0 C)
    (hres : ∀ t ∈ Set.Icc (-1:ℝ) 1, |P t-rootT (1+s t/2) (P t)| ≤ δ)
    (hmodel : ∀ t ∈ Set.Icc (-1:ℝ) 1, |H t-rootHeight (1+s t/2) (P t)| ≤ e) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1, |H t-aS (s t)| ≤ e+5*δ/(17*q₀*(1-rootLambda ⌊q₀⌋₊)) :=
  root_defect_model_transfer s P H q₀ C δ e hq₀ hC hs hq hP hres hmodel

#check root_defect_enclosure
#print axioms root_defect_enclosure
end Blueprint.Thomson.Finite
