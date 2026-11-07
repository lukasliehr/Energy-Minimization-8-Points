import AllS.Units.N_GI.N_cube_k4.N_cube_after_deletion

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_k4_assemble (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hnoE : ∀ v,Fintype.card (ContactNeighbor Y c v)=4 →
      faceCornerCount (boundaryArray Y c hY hc 3) v≠3) :
    HasSpanningCube (actualContactGraph Y c) :=
  cube_k4_cube_after_deletion Y c hY hc hcupper hirr hbound hne hsupport hk hnoE

#print axioms cube_k4_assemble
end Blueprint.Thomson.Tail.Implementation
