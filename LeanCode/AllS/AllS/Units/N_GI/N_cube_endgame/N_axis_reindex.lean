import AllS.Units.N_GI.N_cube_endgame.N_local_descent

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def cubeTetraPermutation (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) where
  toFun := Fin.cases 0 (fun k => (σ.symm k).succ)
  invFun := Fin.cases 0 (fun k => (σ k).succ)
  left_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simp
  right_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simp

theorem cubeSign_formula (i : Fin 4) (k : Fin 3) : cubeSign i k=if i=0 ∨ i=k.succ then 1 else -1 := by
  fin_cases i <;> fin_cases k <;> norm_num [cubeSign] <;> decide

theorem cubeSign_permute (σ : Equiv.Perm (Fin 3)) (i : Fin 4) (k : Fin 3) :
    cubeSign (cubeTetraPermutation σ i) k=cubeSign i (σ k) := by
  simp only [cubeSign_formula]
  induction i using Fin.cases with
  | zero => simp [cubeTetraPermutation]
  | succ i => simp [cubeTetraPermutation,Equiv.symm_apply_eq]

theorem cubeModelA_reindex_axes (e : Fin 3 → Point) (q : Fin 3 → ℝ)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 4) :
    cubeModelA (e ∘ σ) (q ∘ σ) i=cubeModelA e q (cubeTetraPermutation σ.symm i) := by
  unfold cubeModelA
  rw [←Equiv.sum_comp σ (fun k => (cubeSign (cubeTetraPermutation σ.symm i) k*Real.sqrt (q k)) • e k)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply,cubeSign_permute,Equiv.symm_apply_apply]

theorem cubeModelB_reindex_axes (e : Fin 3 → Point) (c : ℝ) (q : Fin 3 → ℝ)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 4) :
    cubeModelB (e ∘ σ) c (q ∘ σ) i=cubeModelB e c q (cubeTetraPermutation σ.symm i) := by
  unfold cubeModelB
  rw [←Equiv.sum_comp σ (fun k => (-c*cubeSign (cubeTetraPermutation σ.symm i) k/Real.sqrt (q k)) • e k)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply,cubeSign_permute,Equiv.symm_apply_apply]

def cubeAxisLabel (label : CubeVertex ≃ Fin 8) (σ : Equiv.Perm (Fin 3)) : CubeVertex ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) (cubeTetraPermutation σ.symm)).trans label

theorem cubeConfiguration_reindex_axes (e : Fin 3 → Point) (label : CubeVertex ≃ Fin 8)
    (c : ℝ) (q : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    cubeConfiguration (e ∘ σ) (cubeAxisLabel label σ) c (q ∘ σ)=cubeConfiguration e label c q := by
  funext i
  obtain ⟨⟨v,j⟩,rfl⟩ := (cubeAxisLabel label σ).surjective i
  have hh : label.symm (cubeAxisLabel label σ (v,j))=(v,cubeTetraPermutation σ.symm j) := by simp [cubeAxisLabel]
  simp only [cubeConfiguration,Function.comp_apply,Equiv.symm_apply_apply,hh]
  fin_cases v
  · change cubeModelA (e ∘ σ) (q ∘ σ) j=cubeModelA e q (cubeTetraPermutation σ.symm j)
    exact cubeModelA_reindex_axes e q σ j
  · change cubeModelB (e ∘ σ) c (q ∘ σ) j=cubeModelB e c q (cubeTetraPermutation σ.symm j)
    exact cubeModelB_reindex_axes e c q σ j

theorem orthonormal_permute (e : Fin 3 → Point) (he : Orthonormal ℝ e) (σ : Equiv.Perm (Fin 3)) :
    Orthonormal ℝ (e ∘ σ) :=
  ⟨fun i => he.1 (σ i),fun i j hij => he.2 (σ.injective.ne hij)⟩

#print axioms cubeConfiguration_reindex_axes
end Blueprint.Thomson.Tail.Implementation
