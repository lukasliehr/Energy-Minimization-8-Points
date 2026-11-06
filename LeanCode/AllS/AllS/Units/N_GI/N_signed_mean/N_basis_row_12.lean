import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_12 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,0,0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![(-1/2),0,0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,(-1/4),0,0],![0,0,0,0]],![![(1/2),0,0,0],![0,0,0,0]],![![0,(-1/4),0,0],![0,0,0,0]]]
def meanBColumnData_12 : Fin 8 → MeanRadical :=
![![(-1/2),(-1/2),0,0],![(1/2),(1/4),0,0],![0,0,0,0],![(-1/2),(-1/4),0,0],![(1/2),(1/2),0,0],![(-1/2),(-1/4),0,0],![0,0,0,0],![(1/2),(1/4),0,0]]

theorem meanBasisColumnData_correct_12 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 12=meanBasisColumnData_12 p b := by decide +kernel

theorem meanBColumnData_correct_12 : ∀p,meanBKernelData 12 p=meanBColumnData_12 p := by decide +kernel

theorem meanFlatIndex_eq_12 : meanFlatIndex 12=(⟨6,by decide⟩,⟨0,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_12 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 12 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 12) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_12,meanBasisColumnData_correct_12]
  change (√(meanScalarWeight (⟨6,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨0,by decide⟩:Fin 2) then meanScalarRaw ⟨6,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_12,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_12 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 12) p=meanRadicalEval (meanBKernelData 12 p) := by
  rw [meanFlatIndex_eq_12,meanBColumnData_correct_12]
  have hpartn : meanPartner (6:Fin 8)=(⟨5,by decide⟩:Fin 8) := by decide +kernel
  have hpart : meanPartner (⟨6,by decide⟩:Fin 8)=(⟨5,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_12,meanRadicalEval,
      hpart,hpartn,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_12
#print axioms meanBVertexKernel_data_12
end Blueprint.Thomson.Tail.Implementation
