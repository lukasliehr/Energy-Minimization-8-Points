import AllS.Units.N_GI.N_cube_k4_noE.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation (degreeThreeVertices)

theorem cube_k4_noE (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4) :
    ∀z,Fintype.card (ContactNeighbor Y c z)=4 → faceCornerCount (boundaryArray Y c hY hc 3) z≠3 :=
  Implementation.cube_k4_noE_assemble Y c hY hc hcupper hirr hbound hne hsupport hk

#print axioms cube_k4_noE
end Blueprint.Thomson.Tail
