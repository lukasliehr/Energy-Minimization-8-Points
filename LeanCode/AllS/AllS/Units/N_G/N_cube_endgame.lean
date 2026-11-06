import AllS.Units.N_GI.N_cube_endgame.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem cube_endgame (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (hc : 0<packingMaxInner Y) (hcub : packingMaxInner Y<7/25)
    (hspan : HasSpanningCube (actualContactGraph Y (packingMaxInner Y))) (hmin : PackingLocalMinimum Y) :
    packingMaxInner Y=packingHeight ∧ Congruent Y packingReference :=
  cube_endgame_assemble Y hY hc hcub hspan hmin

#print axioms cube_endgame
end Blueprint.Thomson.Tail
