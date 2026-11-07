import AllS.Units.N_G.N_exterior_irreducible
import AllS.Units.N_G.N_spanning_cube
import AllS.Units.N_G.N_cube_endgame
import AllS.Units.N_G.N_product_gauge
import AllS.Units.N_GI.N_constants.N_algebra

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem exterior_geometric_localization (H : (Fin 8 → Point) → ℝ) (η : ℝ)
    (hH : ContinuousOn H packingUnitSet)
    (hinv : ∀Y Z,Congruent Y Z → H Y=H Z) (hP : η<H packingReference)
    (hboundary : ¬∃Y,Y∈packingUnitSet ∧ H Y=η ∧ packingMaxInner Y≤packingHeight+33/2000)
    (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) (hb : packingMaxInner Y≤packingHeight+33/2000) : η<H Y := by
  by_contra hn
  have hex : ∃Z,Z∈packingExterior H η ∧ packingMaxInner Z≤packingHeight+33/2000 :=
    ⟨Y,⟨hY,le_of_not_gt hn⟩,hb⟩
  have hcstar : packingHeight+33/2000<1 := by linarith [constants_algebra.2.2.1]
  obtain ⟨Z,hZ,hHZ,hZp,hZb,hlocal,hirr,hcontacts⟩ :=
    exterior_irreducible H η _ hH hcstar hboundary hex
  have hcub : packingMaxInner Z<7/25 := hZb.trans_lt constants_algebra.2.2.1
  have hspan := spanning_cube Z (packingMaxInner Z) hZ hZp (by linarith) hirr
    ((SquareAntiprismVerification.packingMaxInner_le_iff Z _).mp le_rfl) hcontacts
  have hc := (cube_endgame Z hZ hZp hcub hspan hlocal).2
  have he := hinv Z packingReference hc
  linarith

theorem localization_gauge_above_of_boundary
    (hboundary : ¬∃Y,Y∈packingUnitSet ∧ productGauge Y=239/250 ∧ packingMaxInner Y≤packingHeight+33/2000)
    (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) (hb : packingMaxInner Y≤packingHeight+33/2000) :
    (239/250:ℝ)<productGauge Y := by
  apply exterior_geometric_localization productGauge (239/250)
    product_gauge_continuous_extrema.1.continuousOn
    (fun Y Z h=>(gauges_congruence_invariant h).1) ?_ hboundary Y hY hb
  have hp : productGauge packingReference=1 :=
    (productGauge_eq_one_iff packingReference packingReference_norm).mpr
      ⟨LinearIsometryEquiv.refl ℝ Point,Equiv.refl _,fun _=>rfl⟩
  rw [hp]
  norm_num

#print axioms exterior_geometric_localization
#print axioms localization_gauge_above_of_boundary
end Blueprint.Thomson.Tail.Implementation
