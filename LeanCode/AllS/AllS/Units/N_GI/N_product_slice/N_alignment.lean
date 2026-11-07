import AllS.Units.N_GI.N_product_slice.N_slice_stationarity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem attained_product_alignment (Y : Fin 8 → Point) (a : GaugeAction) (ha : a∈gaugeActions)
    (hmax : ∀b∈gaugeActions,gaugeProduct Y b≤gaugeProduct Y a) :
    IsProductAligned (alignedConfiguration Y a) := by
  intro b hb
  exact hmax (gaugeActionCompose b a) (gaugeActionCompose_mem b a hb ha)

theorem product_alignment_exists (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    ∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      let Z : Fin 8 → Point := fun i => U (Y (σ i))
      (∀i,‖Z i‖=1) ∧ IsProductAligned Z ∧ productGauge Z=productGauge Y ∧
      productGauge Y=productObjective Y U σ := by
  obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).1
  have hc : Congruent (alignedConfiguration Y a) Y :=
    ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,fun _ => rfl⟩
  exact ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,alignedConfiguration_norm Y hY a ha,
    attained_product_alignment Y a ha hm,(gauges_congruence_invariant hc).1,he⟩

#print axioms product_alignment_exists
end Blueprint.Thomson.Tail.Implementation
