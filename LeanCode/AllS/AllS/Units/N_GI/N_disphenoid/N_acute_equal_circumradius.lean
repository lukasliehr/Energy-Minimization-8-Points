import AllS.Units.N_GI.N_disphenoid.N_acute_angles

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem disphenoid_acute_equal_circumradius (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    ∀i,∃t : Affine.Triangle ℝ Point,t.points=A ∘ i.succAbove ∧
      t.circumcenter=c • B i ∧ t.circumradius=Real.sqrt (1-c^2) ∧ t.AcuteAngled := by
  intro i
  have hs := polar_tetrahedra_matched_strict A B c hAunit hAinj hBinj hc hcross hmatched
  obtain ⟨t,ht,hctr,hrad⟩ := cube_facet_circumcenter A B c hc hAunit hBunit hAinj hBinj hcross hs i
  obtain ⟨w,hwp,hws,hwr⟩ := cube_projection_positive_coordinates A B c hc hBunit hBinj hcross hs i
  refine ⟨t,ht,hctr,hrad,positive_circumcenter_acuteAngled t (c • B i) w hwp hws ?_ ?_⟩
  · simpa only [ht,Function.comp_apply] using hwr
  · intro j
    simp only [ht,Function.comp_apply]
    exact (cube_facet_radius_sq A B c hAunit hBunit hcross i j).trans
      (cube_facet_radius_sq A B c hAunit hBunit hcross i 0).symm

#print axioms disphenoid_acute_equal_circumradius
end Blueprint.Thomson.Tail.Implementation
