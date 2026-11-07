import AllS.Units.N_G.N_cube_k08
import AllS.Units.N_G.N_cube_k2
import AllS.Units.N_G.N_cube_k4
import AllS.Units.N_G.N_cube_k6

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem spanning_cube_five_cases (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) :
    HasSpanningCube (actualContactGraph Y c) := by
  have hk := (sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport).2.2.2.2
  rcases hk with h0 | h2 | h4 | h6 | h8
  · exact cube_k08_assemble Y c hY hc hcupper hirr hbound hne hsupport (Or.inr h0)
  · exact (cube_k2_impossible Y c hY hc hcupper hirr hbound hne hsupport h2).elim
  · exact Blueprint.Thomson.Tail.cube_k4 Y c hY hc hcupper hirr hbound hne hsupport h4
  · exact cube_k6_has_spanning_cube Y c hY hc hcupper hirr hbound hne hsupport h6
  · exact cube_k08_assemble Y c hY hc hcupper hirr hbound hne hsupport (Or.inl h8)

#print axioms spanning_cube_five_cases
end Blueprint.Thomson.Tail.Implementation
