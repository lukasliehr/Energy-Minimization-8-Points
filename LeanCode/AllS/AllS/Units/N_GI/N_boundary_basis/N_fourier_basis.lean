import AllS.Units.N_GI.N_boundary_basis.N_rotation_gram

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundaryBasisIndex_injective : Function.Injective boundaryBasisIndex := by
  intro j k h
  apply Fin.ext
  exact congrArg (fun x : Fin 16=>x.val) h

theorem boundaryBasis_ne_rotation (j : Fin 13) (k : Fin 3) :
    boundaryBasisIndex j≠boundaryRotationIndex k := by
  intro h
  have := congrArg Fin.val h
  dsimp [boundaryBasisIndex,boundaryRotationIndex] at this
  omega

theorem boundaryFourier_orthonormal : Orthonormal ℝ boundaryFourier :=
  boundaryNormalized_orthonormal.comp boundaryBasisIndex boundaryBasisIndex_injective

theorem boundaryFourier_rotation_inner (j : Fin 13) (k : Fin 3) :
    inner ℝ (boundaryRotation k) (boundaryFourier j)=0 := by
  simp [boundaryRotation,boundaryFourier,boundaryNormalized,inner_smul_right,
    boundaryRaw_gram,Ne.symm (boundaryBasis_ne_rotation j k)]

theorem boundaryFourier_mem_slice (j : Fin 13) : boundaryFourier j∈rotationSlice := by
  rw [mem_rotationSlice_iff]
  exact fun k=>boundaryFourier_rotation_inner j k

theorem boundary_basis_fourier_basis : Orthonormal ℝ boundaryFourier ∧
    (∀j k,inner ℝ (boundaryRotation k) (boundaryFourier j)=0) :=
  ⟨boundaryFourier_orthonormal,boundaryFourier_rotation_inner⟩

#print axioms boundary_basis_fourier_basis
end Blueprint.Thomson.Tail.Implementation
