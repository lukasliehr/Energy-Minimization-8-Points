import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_15 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(-1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(-1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(-1/4),0,0]],![![0,0,0,0],![0,(1/4),0,0]],![![0,0,0,0],![0,(-1/4),0,0]]]
def meanBColumnData_15 : Fin 8 → MeanRadical :=
![![0,0,-1,-1],![0,0,1,1],![0,0,-1,-1],![0,0,1,1],![0,0,-1,-1],![0,0,1,1],![0,0,-1,-1],![0,0,1,1]]

theorem meanBasisColumnData_correct_15 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 15=meanBasisColumnData_15 p b := by decide +kernel

theorem meanBColumnData_correct_15 : ∀p,meanBKernelData 15 p=meanBColumnData_15 p := by decide +kernel

theorem meanFlatIndex_eq_15 : meanFlatIndex 15=(⟨7,by decide⟩,⟨1,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_15 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 15 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 15) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_15,meanBasisColumnData_correct_15]
  change (√(meanScalarWeight (⟨7,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨1,by decide⟩:Fin 2) then meanScalarRaw ⟨7,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_15,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_15 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 15) p=meanRadicalEval (meanBKernelData 15 p) := by
  rw [meanFlatIndex_eq_15,meanBColumnData_correct_15]
  have hpart : meanPartner (⟨7,by decide⟩:Fin 8)=(⟨7,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_15,meanRadicalEval,
      hpart,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_15
#print axioms meanBVertexKernel_data_15
end Blueprint.Thomson.Tail.Implementation
