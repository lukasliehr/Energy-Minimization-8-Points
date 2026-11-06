import AllS.Units.N_GI.N_product_gauge.N_attained_extrema

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] gaugePermutationTopology
local instance : DiscreteTopology (Equiv.Perm (Fin 8)) := ⟨rfl⟩

theorem product_gauge_continuous_extrema : Continuous productGauge ∧ Continuous chordOrbitSquare :=
  ⟨product_gauge_compact_action.continuous_sSup gaugeProduct_continuous,
   product_gauge_compact_action.continuous_sInf gaugeChordSquare_continuous⟩

#print axioms product_gauge_continuous_extrema
end Blueprint.Thomson.Tail.Implementation
