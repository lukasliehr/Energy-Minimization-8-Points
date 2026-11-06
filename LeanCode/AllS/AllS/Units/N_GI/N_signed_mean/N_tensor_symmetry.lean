import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanUniformGramFromU_symm (i j : Fin 16) :
    meanUniformGramFromU i j=meanUniformGramFromU j i := by
  unfold meanUniformGramFromU
  simp only [meanRadicalMul_comm (meanUniformUData i _ _) (meanUniformUData j _ _)]

theorem meanUniformGramData_symm : ∀i j,meanUniformGramData i j=meanUniformGramData j i := by decide +kernel

theorem meanDotKernelData_symm (p : Fin 8) (i j : Fin 16) :
    meanDotKernelData p i j=meanDotKernelData p j i := by
  unfold meanDotKernelData
  simp only [meanRadicalMul_comm (meanBasisData _ i) (meanBasisData _ j)]

theorem meanOrderedKernelData_symm (i j k : Fin 16) :
    meanOrderedKernelData i j k=meanOrderedKernelData i k j := by
  simp only [meanOrderedKernelData,meanDotKernelData_symm _ j k]

theorem meanCubicKernelData_swap12 (i j k : Fin 16) :
    meanCubicKernelData i j k=meanCubicKernelData j i k := by
  unfold meanCubicKernelData
  rw [meanOrderedKernelData_symm k i j]
  congr 1
  abel

theorem meanCubicKernelData_swap23 (i j k : Fin 16) :
    meanCubicKernelData i j k=meanCubicKernelData i k j := by
  unfold meanCubicKernelData
  rw [meanOrderedKernelData_symm i j k]
  congr 1
  abel

theorem meanSymAUData_swap12 (i j k : Fin 16) : meanSymAUData i j k=meanSymAUData j i k := by
  unfold meanSymAUData
  congr 1
  abel

theorem meanSymAUData_swap23 (i j k : Fin 16) : meanSymAUData i j k=meanSymAUData i k j := by
  unfold meanSymAUData
  congr 1
  abel

theorem symmetric_triple_ext {ι β : Type*} [LinearOrder ι]
    (f g : ι → ι → ι → β)
    (hf12 : ∀i j k,f i j k=f j i k) (hf23 : ∀i j k,f i j k=f i k j)
    (hg12 : ∀i j k,g i j k=g j i k) (hg23 : ∀i j k,g i j k=g i k j)
    (h : ∀i j k,i≤j → j≤k → f i j k=g i j k) (i j k : ι) : f i j k=g i j k := by
  by_cases hij : i≤j
  · by_cases hjk : j≤k
    · exact h i j k hij hjk
    · have hkj := le_of_not_ge hjk
      by_cases hik : i≤k
      · rw [hf23 i j k,hg23 i j k]
        exact h i k j hik hkj
      · rw [hf23 i j k,hg23 i j k,hf12 i k j,hg12 i k j]
        exact h k i j (le_of_not_ge hik) hij
  · have hji := le_of_not_ge hij
    by_cases hik : i≤k
    · rw [hf12 i j k,hg12 i j k]
      exact h j i k hji hik
    · have hki := le_of_not_ge hik
      by_cases hjk : j≤k
      · rw [hf12 i j k,hg12 i j k,hf23 j i k,hg23 j i k]
        exact h j k i hjk hki
      · rw [hf12 i j k,hg12 i j k,hf23 j i k,hg23 j i k,hf12 j k i,hg12 j k i]
        exact h k j i (le_of_not_ge hjk) hji

#print axioms symmetric_triple_ext
end Blueprint.Thomson.Tail.Implementation
