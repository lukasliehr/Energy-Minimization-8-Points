import AllS.Units.N_GI.N_cube_k08.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation (degreeThreeVertices HasSpanningCube actualContactGraph)

theorem cube_k08 (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=8 ∨ (degreeThreeVertices Y c).card=0) :
    HasSpanningCube (actualContactGraph Y c) :=
  Implementation.cube_k08_assemble Y c hY hc hcupper hirr hbound hne hsupport hk

#print axioms cube_k08
end Blueprint.Thomson.Tail
