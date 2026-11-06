import AllS.Units.N_GI.N_boundary_basis.N_fourier_basis

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundarySlice_expand (q : TangentCoordinates) (hq : q∈rotationSlice) :
    (∑j,inner ℝ (boundaryFourier j) q • boundaryFourier j)=q := by
  have he := boundaryCompleteBasis_expand q
  have hz (j : Fin 3) : inner ℝ (boundaryNormalized (boundaryRotationIndex j)) q=0 := by
    have h := (mem_rotationSlice_iff q).mp hq j
    simp only [boundaryNormalized,inner_smul_left,starRingEnd_apply,star_trivial]
    change (√(boundaryWeight (boundaryRotationIndex j)))⁻¹*inner ℝ (boundaryRotation j) q=0
    rw [h,mul_zero]
  rw [Fin.sum_univ_add (a:=13) (b:=3)] at he
  have hid (j : Fin 13) : Fin.castAdd 3 j=boundaryBasisIndex j := rfl
  have hjd (j : Fin 3) : Fin.natAdd 13 j=boundaryRotationIndex j := rfl
  simpa only [hid,hjd,hz,zero_smul,Finset.sum_const_zero,add_zero,boundaryFourier] using he

def boundarySliceVector (j : Fin 13) : rotationSlice := ⟨boundaryFourier j,boundaryFourier_mem_slice j⟩

theorem boundarySliceVector_orthonormal : Orthonormal ℝ boundarySliceVector := by
  rw [orthonormal_iff_ite]
  intro j k
  exact orthonormal_iff_ite.mp boundaryFourier_orthonormal j k

theorem boundarySliceVector_spans : ⊤ ≤ Submodule.span ℝ (Set.range boundarySliceVector) := by
  intro q _
  have hq : q=(∑j,inner ℝ (boundaryFourier j) (q : TangentCoordinates) • boundarySliceVector j) := by
    apply Subtype.ext
    simpa [boundarySliceVector] using (boundarySlice_expand (q : TangentCoordinates) q.property).symm
  rw [hq]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

def boundarySliceBasis : OrthonormalBasis (Fin 13) ℝ rotationSlice :=
  OrthonormalBasis.mk boundarySliceVector_orthonormal boundarySliceVector_spans

def boundarySliceEquiv : EuclideanSpace ℝ (Fin 13) ≃ₗᵢ[ℝ] rotationSlice :=
  boundarySliceBasis.repr.symm

theorem boundarySliceEquiv_apply (x : EuclideanSpace ℝ (Fin 13)) :
    (boundarySliceEquiv x : TangentCoordinates)=∑j,x j • boundaryFourier j := by
  have h := (boundarySliceBasis.sum_repr_symm x).symm
  simpa [boundarySliceEquiv,boundarySliceBasis,boundarySliceVector] using congrArg Subtype.val h

theorem boundary_basis_basis_of_slice :
    ∃e : EuclideanSpace ℝ (Fin 13) ≃ₗᵢ[ℝ] rotationSlice,
      ∀x,(e x : TangentCoordinates)=∑j,x j • boundaryFourier j :=
  ⟨boundarySliceEquiv,boundarySliceEquiv_apply⟩

#print axioms boundary_basis_basis_of_slice
end Blueprint.Thomson.Tail.Implementation
