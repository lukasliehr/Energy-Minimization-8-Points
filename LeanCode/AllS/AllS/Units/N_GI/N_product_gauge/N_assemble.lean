import AllS.Units.N_GI.N_product_gauge.N_invariant_and_one

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem gauge_productObjective (Y : Fin 8 → Point) (a : GaugeAction) (ha : a∈gaugeActions) :
    gaugeProduct Y a=productObjective Y (gaugeOrthogonalEquiv a.1 ha.1) a.2 := rfl

theorem product_gauge_assemble (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    Continuous productGauge ∧ Continuous chordOrbitSquare ∧
    (∀Z,Congruent Y Z → productGauge Y=productGauge Z ∧ chordOrbitSquare Y=chordOrbitSquare Z) ∧
    0≤productGauge Y ∧ productGauge Y≤1 ∧ (productGauge Y=1 ↔ Congruent Y packingReference) ∧
    (∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      productGauge Y=productObjective Y U σ ∧ ∀(V : Point ≃ₗᵢ[ℝ] Point)(τ : Equiv.Perm (Fin 8)),
        productObjective Y V τ≤productObjective Y U σ) ∧
    (∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      chordOrbitSquare Y=(∑i,‖U (Y (σ i))-packingReference i‖^2) ∧
      ∀(V : Point ≃ₗᵢ[ℝ] Point)(τ : Equiv.Perm (Fin 8)),
        (∑i,‖U (Y (σ i))-packingReference i‖^2)≤(∑i,‖V (Y (τ i))-packingReference i‖^2)) := by
  obtain ⟨hg,hlo,hup,hone⟩ := product_gauge_invariant_and_one Y hY
  refine ⟨product_gauge_continuous_extrema.1,product_gauge_continuous_extrema.2,hg,hlo,hup,hone,?_,?_⟩
  · obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).1
    refine ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,he,fun V τ => ?_⟩
    exact hm (V.toLinearIsometry.toContinuousLinearMap,τ) ⟨V.norm_map,Set.mem_univ _⟩
  · obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).2
    refine ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,he,fun V τ => ?_⟩
    exact hm (V.toLinearIsometry.toContinuousLinearMap,τ) ⟨V.norm_map,Set.mem_univ _⟩

#print axioms product_gauge_assemble
end Blueprint.Thomson.Tail.Implementation
