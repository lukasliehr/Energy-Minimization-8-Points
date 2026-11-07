import AllS.Units.N_G.N_boundary_polynomials

noncomputable section
open SquareAntiprismVerification (packingMaxInner)
namespace Blueprint.Thomson.Tail.Implementation

/-- The exact residual-corrected boundary certificate must prove this proposition.
This definition is not an assumed certificate or an axiom. -/
def BoundarySOSInfeasible : Prop :=
  ¬∃y : Fin 13 → ℝ,
    3620/3721≤(∑j,boundaryDiagonal j*(y j)^2) ∧ (∑j,boundaryDiagonal j*(y j)^2)≤1 ∧
    ∀e : ContactIndex,0≤boundaryContactPolynomial e y

theorem boundary_infeasible_of_checked_polynomials (hcap : BoundarySOSInfeasible) :
    ¬∃Y,Y∈{Z : Fin 8 → Point | ∀i,‖Z i‖=1} ∧ productGauge Y=239/250 ∧
      packingMaxInner Y≤packingHeight+33/2000 := by
  rintro ⟨Y,hY,hg,hm⟩
  exact hcap (boundary_polynomials Y hY hg hm)

theorem productBoundarySpec_of_checked_polynomials (hcap : BoundarySOSInfeasible) : ProductBoundarySpec := by
  intro Y hY hb hex
  obtain ⟨U,σ,he,hmax⟩ := hex
  obtain ⟨_,_,_,_,_,_,⟨V,τ,hatt,_⟩,_⟩ := product_gauge_assemble Y hY
  have hlo : productObjective Y U σ≤productGauge Y :=
    gaugeProduct_le_productGauge Y (U.toLinearIsometry.toContinuousLinearMap,σ)
      ⟨U.norm_map,Set.mem_univ _⟩
  have hhi : productGauge Y≤productObjective Y U σ := by rw [hatt]; exact hmax V τ
  have hg : productGauge Y=239/250 := (le_antisymm hhi hlo).trans he
  have hm : packingMaxInner Y≤packingHeight+33/2000 := by
    apply (SquareAntiprismVerification.packingMaxInner_le_iff Y _).mpr
    intro i j hij
    have h := hb i j hij
    dsimp [gap] at h
    linarith
  exact boundary_infeasible_of_checked_polynomials hcap ⟨Y,hY,hg,hm⟩

#print axioms productBoundarySpec_of_checked_polynomials
end Blueprint.Thomson.Tail.Implementation
