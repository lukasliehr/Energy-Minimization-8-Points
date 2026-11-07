import AllS.Units.N_GI.N_boundary_basis.N_rationalized_columns

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_basis_assemble :
    Orthonormal ℝ boundaryFourier ∧
    (∃e : EuclideanSpace ℝ (Fin 13) ≃ₗᵢ[ℝ] rotationSlice,
      ∀x,(e x : TangentCoordinates)=∑j,x j • boundaryFourier j) ∧
    (∀j k,inner ℝ (boundaryScaled j) (boundaryScaled k)=if j=k then boundaryDiagonal j else 0) ∧
    (∀j i,boundaryPhysical j i= !₂[boundaryTriple j i 0/packingRadius,
      boundaryTriple j i 1/packingRadius,boundaryTriple j i 2/packingZHeight]) ∧
    (∀i k j,inner ℝ (packingReference i) (boundaryPhysical j k)=
      angularCos i*boundaryTriple j k 0+angularSin i*boundaryTriple j k 1+layerSign i*boundaryTriple j k 2) ∧
    (∀i k j l,inner ℝ (boundaryPhysical j i) (boundaryPhysical l k)=
      boundaryZ*(boundaryTriple j i 0*boundaryTriple l k 0+boundaryTriple j i 1*boundaryTriple l k 1)+
      (1+2*√2)*boundaryTriple j i 2*boundaryTriple l k 2) ∧
    (∀q∈rotationSlice,∃y : Fin 13 → ℝ,boundarySynthesis y=q) ∧
    (∀y,‖boundarySynthesis y‖^2=∑j,boundaryDiagonal j*(y j)^2) :=
  ⟨boundaryFourier_orthonormal,boundary_basis_basis_of_slice,boundaryScaled_gram,
    boundaryPhysical_triple,boundary_reference_dot,boundary_physical_dot,boundarySynthesis_surjective,boundarySynthesis_norm_sq⟩

#print axioms boundary_basis_assemble
end Blueprint.Thomson.Tail.Implementation
