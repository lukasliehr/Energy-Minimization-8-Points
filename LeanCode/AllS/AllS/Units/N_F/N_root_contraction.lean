import AllS.Units.N_FI.N_root_contraction.N_lipschitz

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem stationary_root_contraction (s q₀ : ℝ) (hs : 0 ≤ s) (hq₀ : 1 ≤ q₀)
    (hq : q₀ ≤ 1+s/2) :
    rootV s ∈ Set.Icc 0 rootC ∧ rootT (1+s/2) (rootV s)=rootV s ∧
    rootHeight (1+s/2) (rootV s)=aS s ∧ rootLambda ⌊q₀⌋₊ < 1 ∧
    (∀ v ∈ Set.Icc 0 rootC, HasDerivAt (rootHeight (1+s/2)) (rootHeightDeriv (1+s/2) v) v ∧
      |rootHeightDeriv (1+s/2) v| ≤ 5/(17*q₀)) ∧
    (∀ v ∈ Set.Icc 0 rootC, ∀ w ∈ Set.Icc 0 rootC,
      |rootT (1+s/2) v-rootT (1+s/2) w| ≤ rootLambda ⌊q₀⌋₊*|v-w| ∧
      |rootHeight (1+s/2) v-rootHeight (1+s/2) w| ≤ 5*|v-w|/(17*q₀)) := by
  obtain ⟨hv,hT,hh⟩ := aS_root_coordinates s hs
  refine ⟨hv,hT,hh,(rootLambda_bounds _).2,?_,?_⟩
  · intro v _hv
    obtain ⟨hd,hp,hb⟩ := root_contraction_derivative_height (1+s/2) q₀ v hq₀ hq
    exact ⟨hd,by rwa [abs_of_pos hp]⟩
  · intro v hv w hw
    exact root_contraction_lipschitz (1+s/2) q₀ v w hq₀ hq hv hw

#check stationary_root_contraction
#print axioms stationary_root_contraction
end Blueprint.Thomson.Finite
