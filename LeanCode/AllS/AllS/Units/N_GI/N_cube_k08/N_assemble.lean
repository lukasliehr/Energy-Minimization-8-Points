import AllS.Units.N_GI.N_cube_k08.N_all_cubic
import AllS.Units.N_GI.N_cube_k08.N_two_squares

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_k08_assemble (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=8 ∨ (degreeThreeVertices Y c).card=0) :
    HasSpanningCube (actualContactGraph Y c) := by
  rcases hk with h8 | h0
  · exact cube_k08_all_cubic Y c hY hc hcupper hirr hbound hne hsupport h8
  · exact cube_k08_delete_matching Y c hY hc hcupper hirr hbound hne hsupport h0

#print axioms cube_k08_assemble
end Blueprint.Thomson.Tail.Implementation
