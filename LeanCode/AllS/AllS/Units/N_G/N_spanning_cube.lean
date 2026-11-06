import AllS.Units.N_GI.N_spanning_cube.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation (HasSpanningCube actualContactGraph)

theorem spanning_cube (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty) : HasSpanningCube (actualContactGraph Y c) :=
  Implementation.spanning_cube_assemble Y c hY hc hcupper hirr hbound hne

#print axioms spanning_cube
end Blueprint.Thomson.Tail
