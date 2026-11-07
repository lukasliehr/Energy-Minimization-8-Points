import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_0 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]]]
def meanBColumnData_0 : Fin 8 → MeanRadical :=
![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]

theorem meanBasisColumnData_correct_0 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 0=meanBasisColumnData_0 p b := by decide +kernel

theorem meanBColumnData_correct_0 : ∀p,meanBKernelData 0 p=meanBColumnData_0 p := by decide +kernel

theorem meanFlatIndex_eq_0 : meanFlatIndex 0=(⟨0,by decide⟩,⟨0,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_0 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 0 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 0) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_0,meanBasisColumnData_correct_0]
  change (√(meanScalarWeight (⟨0,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨0,by decide⟩:Fin 2) then meanScalarRaw ⟨0,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_0,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_0 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 0) p=meanRadicalEval (meanBKernelData 0 p) := by
  rw [meanFlatIndex_eq_0,meanBColumnData_correct_0]
  have hpart : meanPartner (⟨0,by decide⟩:Fin 8)=(⟨0,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_0,meanRadicalEval,
      hpart,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_0
#print axioms meanBVertexKernel_data_0
end Blueprint.Thomson.Tail.Implementation
