import AllS.Units.N_GI.N_signed_mean.N_block_basis

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def meanScalarCoefficient (b : Fin 8 → ℝ) (j : Fin 8) : ℝ :=
  (∑i,meanScalarRaw j i*b i)/meanScalarWeight j

theorem meanScalarCoefficient_synthesis (y : Fin 8 → ℝ) (j : Fin 8) :
    meanScalarCoefficient (meanScalarSynthesis y) j=y j := by
  have h (k : Fin 8) : (∑i,meanScalarRaw j i*(y k*meanScalarRaw k i))=
      y k*(if j=k then meanScalarWeight j else 0) := by
    rw [← meanScalarRaw_gram,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold meanScalarCoefficient meanScalarSynthesis
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [h]
  simp [meanScalarWeight_pos j |>.ne',mul_ite]

theorem meanScalarExpansion (b : Fin 8 → ℝ) : meanScalarSynthesis (meanScalarCoefficient b)=b := by
  obtain ⟨y,rfl⟩ := meanScalarSynthesis_surjective b
  have he : meanScalarCoefficient (meanScalarSynthesis y)=y := funext (meanScalarCoefficient_synthesis y)
  rw [he]

theorem stressB_normalized_coefficients (j : Fin 8 × Fin 2) (b : Fin 8 → ℝ) :
    stressB (meanTangentNormalized j) b=
      meanNormalization j.1*(∑k,meanScalarCoefficient b k*meanBEntry j k) := by
  unfold meanTangentNormalized
  rw [stressB_smul_left,meanNormalization_eq]
  congr 1
  conv_lhs => rw [← meanScalarExpansion b]
  unfold meanScalarSynthesis
  rw [stressB_sum_right]
  simp_rw [stressB_smul_right,meanB_raw]

theorem meanPartner_weight (j : Fin 8) : meanScalarWeight (meanPartner j)=meanScalarWeight j := by
  fin_cases j <;> norm_num [meanPartner,meanScalarWeight,Fin.ext_iff]

def meanBVertexKernel (j : Fin 8 × Fin 2) (p : Fin 8) : ℝ :=
  meanNormalization j.1*(if j.2=0 then
    -meanBetaFactor j.1*meanSinSign j.1*meanScalarRaw (meanPartner j.1) p
  else packingZHeight*meanRadialFactor j.1*meanScalarRaw j.1 p)

theorem stressB_vertex_kernel (j : Fin 8 × Fin 2) (b : Fin 8 → ℝ) :
    stressB (meanTangentNormalized j) b=packingRadius*(∑p,meanBVertexKernel j p*b p) := by
  rw [stressB_normalized_coefficients]
  have hw := (meanScalarWeight_pos j.1).ne'
  by_cases hj : j.2=0
  · simp [meanBEntry,hj,meanScalarCoefficient,meanBVertexKernel,meanPartner_weight]
    field_simp
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  · simp [meanBEntry,hj,meanScalarCoefficient,meanBVertexKernel]
    field_simp
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring

#print axioms stressB_vertex_kernel
end Blueprint.Thomson.Tail.Implementation
