import AllS.Units.N_GI.N_localization.N_gauge_reduction
import AllS.Units.N_GI.N_localization.N_inner_cutoff
import AllS.Units.N_GI.N_localization.N_rational_log_bound
import AllS.Units.N_GI.N_boundary_infeasible.N_certificate_interface

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem gauge_boundary_exclusion_of_spec (hboundary : ProductBoundarySpec) :
    ¬∃Y,Y∈packingUnitSet ∧ productGauge Y=239/250 ∧ packingMaxInner Y≤packingHeight+33/2000 := by
  rintro ⟨Y,hY,hg,hm⟩
  have hb : ∀i j,i≠j → inner ℝ (Y i) (Y j)≤packingHeight+gap/2 := by
    intro i j hij
    have h := (SquareAntiprismVerification.packingMaxInner_le_iff Y _).mp hm i j hij
    dsimp [gap]
    linarith
  obtain ⟨_,_,_,_,_,_,⟨U,σ,hatt,hmax⟩,_⟩ := product_gauge_assemble Y hY
  exact hboundary Y hY hb ⟨U,σ,hatt.symm.trans hg,hmax⟩

theorem localization_from_productBoundarySpec (hboundary : ProductBoundarySpec) : LocalizationSpec := by
  intro Y hY hd
  have hm := localization_inner_cutoff Y hY hd
  have hg := localization_gauge_above_of_boundary (gauge_boundary_exclusion_of_spec hboundary) Y hY hm
  have hr := localization_rational_log_bound Y hY hg.le
  obtain ⟨U,σ,hZ,he,_,_⟩ := chord_alignment_exists Y hY
  refine ⟨U,σ,?_⟩
  change chordSquare (fun i=>U (Y (σ i)))<radius^2
  rw [he,←chordOrbitRadius_sq Y hY]
  have hp : 0≤chordOrbitRadius Y := Real.sqrt_nonneg _
  dsimp [radius]
  nlinarith

theorem localization_from_checked_polynomials (hcap : BoundarySOSInfeasible) : LocalizationSpec :=
  localization_from_productBoundarySpec (productBoundarySpec_of_checked_polynomials hcap)

#print axioms localization_from_productBoundarySpec
#print axioms localization_from_checked_polynomials
end Blueprint.Thomson.Tail.Implementation
