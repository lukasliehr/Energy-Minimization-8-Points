import AllS.Units.N_GI.N_product_gauge.N_assemble

namespace Blueprint.Thomson.Tail
open Implementation
theorem product_gauge (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    Continuous productGauge ∧ Continuous chordOrbitSquare ∧
    (∀Z,Congruent Y Z → productGauge Y=productGauge Z ∧ chordOrbitSquare Y=chordOrbitSquare Z) ∧
    0≤productGauge Y ∧ productGauge Y≤1 ∧ (productGauge Y=1 ↔ Congruent Y packingReference) ∧
    (∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      productGauge Y=productObjective Y U σ ∧ ∀(V : Point ≃ₗᵢ[ℝ] Point)(τ : Equiv.Perm (Fin 8)),
        productObjective Y V τ≤productObjective Y U σ) ∧
    (∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      chordOrbitSquare Y=(∑i,‖U (Y (σ i))-packingReference i‖^2) ∧
      ∀(V : Point ≃ₗᵢ[ℝ] Point)(τ : Equiv.Perm (Fin 8)),
        (∑i,‖U (Y (σ i))-packingReference i‖^2)≤(∑i,‖V (Y (τ i))-packingReference i‖^2)) := Implementation.product_gauge_assemble Y hY

#print axioms product_gauge
end Blueprint.Thomson.Tail
