import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_11 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![(-1/2),0,0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![0,(-1/4),0,0]],![![0,0,0,0],![(1/2),0,0,0]],![![0,0,0,0],![0,(-1/4),0,0]]]
def meanBColumnData_11 : Fin 8 → MeanRadical :=
![![0,0,0,0],![0,0,(-1/2),(-1/4)],![0,0,(1/2),(1/2)],![0,0,(-1/2),(-1/4)],![0,0,0,0],![0,0,(1/2),(1/4)],![0,0,(-1/2),(-1/2)],![0,0,(1/2),(1/4)]]

theorem meanBasisColumnData_correct_11 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 11=meanBasisColumnData_11 p b := by decide +kernel

theorem meanBColumnData_correct_11 : ∀p,meanBKernelData 11 p=meanBColumnData_11 p := by decide +kernel

theorem meanFlatIndex_eq_11 : meanFlatIndex 11=(⟨6,by decide⟩,⟨1,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_11 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 11 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 11) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_11,meanBasisColumnData_correct_11]
  change (√(meanScalarWeight (⟨6,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨1,by decide⟩:Fin 2) then meanScalarRaw ⟨6,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_11,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_11 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 11) p=meanRadicalEval (meanBKernelData 11 p) := by
  rw [meanFlatIndex_eq_11,meanBColumnData_correct_11]
  have hpart : meanPartner (⟨6,by decide⟩:Fin 8)=(⟨5,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_11,meanRadicalEval,
      hpart,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_11
#print axioms meanBVertexKernel_data_11
end Blueprint.Thomson.Tail.Implementation
