import AllS.Units.N_GI.N_covering.N_sphere_covered

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem covering_no_rattlers (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    ∀ k, ∃ j, j ≠ k ∧ inner ℝ (Y k) (Y j) = c := by
  intro k
  obtain ⟨C, hk⟩ := covering_sphere_covered Y c hY hc hcupper hirr hne hsupport
    (Y k) (hY.1 k)
  obtain ⟨i, hi⟩ := covering_region_configuration_vertex C hirr hcupper hbound (hsupport C) k hk
  simpa only [hi] using C.vertex_nonisolated i

#print axioms covering_no_rattlers

end Blueprint.Thomson.Tail.Implementation
