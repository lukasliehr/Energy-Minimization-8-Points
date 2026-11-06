import AllS.Units.N_GI.N_centered_quadratic.N_projected_form

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundaryRotation_mean (j : Fin 3) : boundaryRotation j=
    (![(-packingZHeight) • meanTangentRaw (5,0)-meanTangentRaw (6,1),
      packingZHeight • meanTangentRaw (6,0)-meanTangentRaw (5,1),
      packingRadius • meanTangentRaw (0,0)] : Fin 3 → TangentCoordinates) j := by
  fin_cases j <;> ext i <;> rcases i with ⟨i,b⟩ <;> fin_cases b <;>
    simp [boundaryRotation,boundaryRotationIndex,boundaryRaw,boundaryRawPair,meanTangentRaw,meanScalarRaw,
      PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] <;> ring

theorem stressH_sub_right (q u v : TangentCoordinates) : stressH q (u-v)=stressH q u-stressH q v := by
  rw [← stressMap_inner_symm,inner_sub_right,stressMap_inner_symm,stressMap_inner_symm]

theorem stressH_raw_rotation (k : Fin 8 × Fin 2) (j : Fin 3) :
    stressH (meanTangentRaw k) (boundaryRotation j)=0 := by
  rw [boundaryRotation_mean]
  have hsm (c : ℝ) (u v : TangentCoordinates) : stressH u (c • v)=c*stressH u v := by
    rw [stressH_symm,stressH_smul_left,stressH_symm]
  fin_cases j
  all_goals
    first
    | change stressH (meanTangentRaw k) ((-packingZHeight) • meanTangentRaw (5,0)-meanTangentRaw (6,1))=0
    | change stressH (meanTangentRaw k) (packingZHeight • meanTangentRaw (6,0)-meanTangentRaw (5,1))=0
    | change stressH (meanTangentRaw k) (packingRadius • meanTangentRaw (0,0))=0
    simp only [stressH_sub_right,hsm,meanH_raw]
  all_goals
    rcases k with ⟨k,b⟩
    fin_cases k <;> fin_cases b <;>
      norm_num [meanHEntry,meanScalarWeight,meanPartner,meanPhiEigen,meanMeridianEigen,meanBetaFactor,
        meanSinSign,Fin.ext_iff] <;>
      ring_nf <;> simp [packing_parameters.2.2.1,packingHeight,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring_nf <;> norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem stressMap_mem_rotationSlice (q : TangentCoordinates) : stressMap q∈rotationSlice := by
  rw [mem_rotationSlice_iff_normalized]
  intro j
  obtain ⟨x,rfl⟩ := meanTangentSynthesis_surjective q
  rw [stressMap_inner]
  rw [stressH_symm]
  unfold meanTangentSynthesis
  rw [stressH_sum_left]
  apply Finset.sum_eq_zero
  intro k _
  rw [stressH_smul_left,normalizedRotation,boundaryNormalized,stressH_symm,stressH_smul_left,stressH_symm]
  change x k*((√(boundaryWeight (boundaryRotationIndex j)))⁻¹*stressH (meanTangentRaw k) (boundaryRotation j))=0
  rw [stressH_raw_rotation]
  ring

#print axioms stressMap_mem_rotationSlice
end Blueprint.Thomson.Tail.Implementation
