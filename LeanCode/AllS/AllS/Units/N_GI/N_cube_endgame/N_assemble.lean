import AllS.Units.N_GI.N_cube_endgame.N_antiprism_congruence

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_endgame_assemble (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (hc : 0<packingMaxInner Y) (hcub : packingMaxInner Y<7/25)
    (hspan : HasSpanningCube (actualContactGraph Y (packingMaxInner Y))) (hmin : PackingLocalMinimum Y) :
    packingMaxInner Y=packingHeight ∧ Congruent Y packingReference :=
  ⟨(cube_endgame_only_double_active Y hY _ rfl hc hcub hspan hmin).1,
    cube_endgame_antiprism_congruence Y hY _ rfl hc hcub hspan hmin⟩

#print axioms cube_endgame_assemble
end Blueprint.Thomson.Tail.Implementation
