import AllS.Units.N_GI.N_cube_k2.N_impossible

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation (degreeThreeVertices)

theorem cube_k2 (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=2) : False :=
  Implementation.cube_k2_impossible Y c hY hc hcupper hirr hbound hne hsupport hk

#print axioms cube_k2
end Blueprint.Thomson.Tail
