import AllS.Units.N_GI.N_spanning_cube.N_five_cases
import AllS.Units.N_G.N_boundary_support

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem spanning_cube_assemble (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty) : HasSpanningCube (actualContactGraph Y c) := by
  have hc01 : c∈Set.Ioo (0:ℝ) 1 := ⟨hc,by linarith⟩
  exact spanning_cube_five_cases Y c hY hc01 hcupper hirr hbound hne
    (fun C => boundary_support_assemble C hcupper hbound hirr)

#print axioms spanning_cube_assemble
end Blueprint.Thomson.Tail.Implementation
