import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_1 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]]]
def meanBColumnData_1 : Fin 8 → MeanRadical :=
![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]

theorem meanBasisColumnData_correct_1 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 1=meanBasisColumnData_1 p b := by decide +kernel

theorem meanBColumnData_correct_1 : ∀p,meanBKernelData 1 p=meanBColumnData_1 p := by decide +kernel

theorem meanFlatIndex_eq_1 : meanFlatIndex 1=(⟨0,by decide⟩,⟨1,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_1 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 1 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 1) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_1,meanBasisColumnData_correct_1]
  change (√(meanScalarWeight (⟨0,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨1,by decide⟩:Fin 2) then meanScalarRaw ⟨0,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_1,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_1 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 1) p=meanRadicalEval (meanBKernelData 1 p) := by
  rw [meanFlatIndex_eq_1,meanBColumnData_correct_1]
  have hpart : meanPartner (⟨0,by decide⟩:Fin 8)=(⟨0,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_1,meanRadicalEval,
      hpart,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_1
#print axioms meanBVertexKernel_data_1
end Blueprint.Thomson.Tail.Implementation
