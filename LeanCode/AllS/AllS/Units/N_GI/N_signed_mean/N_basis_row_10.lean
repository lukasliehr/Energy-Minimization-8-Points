import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_10 : Fin 8 → Fin 2 → MeanRadical :=
![![![(1/2),0,0,0],![0,0,0,0]],![![0,(-1/4),0,0],![0,0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![(-1/2),0,0,0],![0,0,0,0]],![![0,(1/4),0,0],![0,0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,(-1/4),0,0],![0,0,0,0]]]
def meanBColumnData_10 : Fin 8 → MeanRadical :=
![![0,0,0,0],![(1/2),(1/4),0,0],![(-1/2),(-1/2),0,0],![(1/2),(1/4),0,0],![0,0,0,0],![(-1/2),(-1/4),0,0],![(1/2),(1/2),0,0],![(-1/2),(-1/4),0,0]]

theorem meanBasisColumnData_correct_10 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 10=meanBasisColumnData_10 p b := by decide +kernel

theorem meanBColumnData_correct_10 : ∀p,meanBKernelData 10 p=meanBColumnData_10 p := by decide +kernel

theorem meanFlatIndex_eq_10 : meanFlatIndex 10=(⟨5,by decide⟩,⟨0,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_10 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 10 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 10) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_10,meanBasisColumnData_correct_10]
  change (√(meanScalarWeight (⟨5,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨0,by decide⟩:Fin 2) then meanScalarRaw ⟨5,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_10,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_10 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 10) p=meanRadicalEval (meanBKernelData 10 p) := by
  rw [meanFlatIndex_eq_10,meanBColumnData_correct_10]
  have hpartn : meanPartner (5:Fin 8)=(⟨6,by decide⟩:Fin 8) := by decide +kernel
  have hpart : meanPartner (⟨5,by decide⟩:Fin 8)=(⟨6,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_10,meanRadicalEval,
      hpart,hpartn,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_10
#print axioms meanBVertexKernel_data_10
end Blueprint.Thomson.Tail.Implementation
