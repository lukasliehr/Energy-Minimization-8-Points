import AllS.Units.N_GI.N_boundary_basis.N_definitions

noncomputable section
open Real
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

set_option maxHeartbeats 4000000 in
theorem boundaryRotation_vertex (q : TangentCoordinates) (i : Fin 8) (j : Fin 3) :
    (crossVec (packingReference i) (tangentVector q i)) j=
      boundaryRawPair (boundaryRotationIndex j) i 0*q (i,0)+
      boundaryRawPair (boundaryRotationIndex j) i 1*q (i,1) := by
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  have hs : packingZHeight^2+packingRadius^2=1 := by linarith
  have hc := (angular_unit i).1
  have hf : crossVec (packingReference i) (azimuthFrame i)=
      !₂[-layerSign i*packingZHeight*angularCos i,
        -layerSign i*packingZHeight*angularSin i,packingRadius] := by
    rw [packingReference_formula]
    ext j
    fin_cases j <;> simp [crossVec,azimuthFrame] <;>
      first | ring1 | linear_combination packingRadius*hc
  have hg : crossVec (packingReference i) (meridianFrame i)=
      !₂[layerSign i*angularSin i,-layerSign i*angularCos i,0] := by
    rw [packingReference_formula]
    ext j
    fin_cases j <;> simp [crossVec,meridianFrame] <;>
      first
      | ring1
      | linear_combination layerSign i*angularSin i*hs
      | linear_combination -layerSign i*angularCos i*hs
  simp only [tangentVector,crossVec_add_right,SquareAntiprismVerification.crossVec_smul_right,hf,hg]
  fin_cases j <;> simp [boundaryRawPair,boundaryRotationIndex,boundaryCos3,boundarySin3] <;> ring

theorem boundaryRotation_inner (q : TangentCoordinates) (j : Fin 3) :
    (rotationVector q) j=inner ℝ (boundaryRotation j) q := by
  simp only [rotationVector,WithLp.ofLp_sum,Finset.sum_apply,boundaryRotation_vertex]
  simp only [boundaryRotation,boundaryRaw,PiLp.inner_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
    Real.inner_apply]


theorem mem_rotationSlice_iff (q : TangentCoordinates) :
    q∈rotationSlice ↔ ∀j,inner ℝ (boundaryRotation j) q=0 := by
  change rotationVector q=0 ↔ _
  constructor
  · intro h j
    rw [←boundaryRotation_inner,h]
    rfl
  · intro h
    ext j
    simpa [boundaryRotation_inner] using h j

#print axioms boundaryRotation_inner
end Blueprint.Thomson.Tail.Implementation
