import AllS.Units.N_GI.N_slice_point_bound.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail

theorem slice_point_bound (q : TangentCoordinates) (hq : q∈rotationSlice) (i : Fin 8) :
    ‖tangentVector q i‖^2 ≤ (1-Real.sqrt 2/8)*(∑ j : Fin 8, ‖tangentVector q j‖^2) :=
  Implementation.slice_point_bound_assemble q hq i

#print axioms slice_point_bound
end Blueprint.Thomson.Tail
