import AllS.Units.N_GI.N_cube_k08.N_all_equal

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_k08_two_squares (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=0) : SquareAntiprismVerification.Congruent Y P :=
  cube_k08_zero_rigid Y c hY hc hcupper hirr hbound hne hsupport hk

#print axioms cube_k08_two_squares
end Blueprint.Thomson.Tail.Implementation
