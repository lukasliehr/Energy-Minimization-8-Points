import AllS.Units.N_GI.N_boundary_basis.N_physical_columns

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundarySynthesis (y : Fin 13 → ℝ) : TangentCoordinates := ∑j,y j • boundaryScaled j

theorem boundarySynthesis_mem_slice (y : Fin 13 → ℝ) : boundarySynthesis y∈rotationSlice := by
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.smul_mem _ _ (boundaryFourier_mem_slice j)

theorem boundarySynthesis_surjective (q : TangentCoordinates) (hq : q∈rotationSlice) :
    ∃y : Fin 13 → ℝ,boundarySynthesis y=q := by
  refine ⟨fun j=>inner ℝ (boundaryFourier j) q/√(boundaryDiagonal j),?_⟩
  rw [boundarySynthesis]
  calc
    _ = ∑j,inner ℝ (boundaryFourier j) q • boundaryFourier j := by
      apply Finset.sum_congr rfl
      intro j _
      have hn : √(boundaryDiagonal j)≠0 := ne_of_gt (Real.sqrt_pos.mpr (boundaryDiagonal_pos j))
      simp [boundaryScaled,smul_smul,hn]
    _ = q := boundarySlice_expand q hq

theorem boundarySynthesis_norm_sq (y : Fin 13 → ℝ) :
    ‖boundarySynthesis y‖^2=∑j,boundaryDiagonal j*(y j)^2 := by
  rw [←real_inner_self_eq_norm_sq,boundarySynthesis]
  simp only [inner_sum,sum_inner,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_trivial,boundaryScaled_gram]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tangentVector_sum {ι : Type*} (s : Finset ι) (q : ι → TangentCoordinates) (i : Fin 8) :
    tangentVector (∑j∈s,q j) i=∑j∈s,tangentVector (q j) i := by
  classical
  simp only [tangentVector,WithLp.ofLp_sum,Finset.sum_apply,Finset.sum_smul,Finset.sum_add_distrib]

theorem boundarySynthesis_tangent (y : Fin 13 → ℝ) (i : Fin 8) :
    tangentVector (boundarySynthesis y) i=∑j,y j • boundaryPhysical j i := by
  simp only [boundarySynthesis,tangentVector_sum,tangentVector_smul,boundaryPhysical]

#print axioms boundarySynthesis_surjective
#print axioms boundarySynthesis_norm_sq
end Blueprint.Thomson.Tail.Implementation
