import AllS.Units.N_GI.N_boundary_basis.N_normalized
import AllS.Units.N_GI.N_boundary_basis.N_rotation_coordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundaryRotationIndex_injective : Function.Injective boundaryRotationIndex := by
  intro j k h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [boundaryRotationIndex] at this
  omega

theorem boundaryRaw_linearIndependent : LinearIndependent ℝ boundaryRaw := by
  have h := boundaryNormalized_orthonormal.linearIndependent.units_smul
    (fun j=>Units.mk0 (√(boundaryWeight j)) (ne_of_gt (Real.sqrt_pos.mpr (boundaryWeight_pos j))))
  convert! h using 1
  ext j
  simp [boundaryNormalized,smul_smul,(ne_of_gt (Real.sqrt_pos.mpr (boundaryWeight_pos j)))]

theorem boundary_basis_rotation_gram :
    (∀j k,inner ℝ (boundaryRotation j) (boundaryRotation k)=
      if j=k then (![4*(1+packingHeight),4*(1+packingHeight),8*(1-packingHeight)] : Fin 3 → ℝ) j else 0) ∧
    LinearIndependent ℝ boundaryRotation := by
  refine ⟨?_,boundaryRaw_linearIndependent.comp boundaryRotationIndex boundaryRotationIndex_injective⟩
  intro j k
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  simp only [boundaryRotation,boundaryRaw_gram,boundaryRotationIndex_injective.eq_iff]
  fin_cases j <;> fin_cases k <;> norm_num [boundaryWeight,boundaryRotationIndex,hH,hR]

#print axioms boundary_basis_rotation_gram
end Blueprint.Thomson.Tail.Implementation
