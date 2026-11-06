import AllS.Units.N_GI.N_product_gauge.N_compact_action

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] gaugePermutationTopology
local instance : DiscreteTopology (Equiv.Perm (Fin 8)) := ⟨rfl⟩

theorem product_gauge_attained_extrema (Y : Fin 8 → Point) :
    (∃a∈gaugeActions,productGauge Y=gaugeProduct Y a ∧ ∀b∈gaugeActions,gaugeProduct Y b≤gaugeProduct Y a) ∧
    (∃a∈gaugeActions,chordOrbitSquare Y=gaugeChordSquare Y a ∧ ∀b∈gaugeActions,gaugeChordSquare Y a≤gaugeChordSquare Y b) := by
  constructor
  · exact product_gauge_compact_action.exists_sSup_image_eq_and_ge gaugeActions_nonempty
      (gaugeProduct_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  · exact product_gauge_compact_action.exists_sInf_image_eq_and_le gaugeActions_nonempty
      (gaugeChordSquare_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn

theorem gaugeProduct_le_productGauge (Y : Fin 8 → Point) (a : GaugeAction) (ha : a∈gaugeActions) :
    gaugeProduct Y a≤productGauge Y := by
  obtain ⟨b,hb,he,hm⟩ := (product_gauge_attained_extrema Y).1
  rw [he]
  exact hm a ha

theorem chordOrbitSquare_le_gaugeChordSquare (Y : Fin 8 → Point) (a : GaugeAction) (ha : a∈gaugeActions) :
    chordOrbitSquare Y≤gaugeChordSquare Y a := by
  obtain ⟨b,hb,he,hm⟩ := (product_gauge_attained_extrema Y).2
  rw [he]
  exact hm a ha

#print axioms product_gauge_attained_extrema
end Blueprint.Thomson.Tail.Implementation
