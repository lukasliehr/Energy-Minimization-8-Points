import AllS.Units.N_GI.N_signed_mean.N_flat_basis
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBasisColumnData_7 : Fin 8 → Fin 2 → MeanRadical :=
![![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![(1/2),0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![(-1/2),0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![(1/2),0,0,0]],![![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![(-1/2),0,0,0]]]
def meanBColumnData_7 : Fin 8 → MeanRadical :=
![![0,0,0,0],![0,0,1,(1/2)],![0,0,0,0],![0,0,-1,(-1/2)],![0,0,0,0],![0,0,1,(1/2)],![0,0,0,0],![0,0,-1,(-1/2)]]

theorem meanBasisColumnData_correct_7 : ∀p b,
    meanBasisData (finProdFinEquiv (p,b)) 7=meanBasisColumnData_7 p b := by decide +kernel

theorem meanBColumnData_correct_7 : ∀p,meanBKernelData 7 p=meanBColumnData_7 p := by decide +kernel

theorem meanFlatIndex_eq_7 : meanFlatIndex 7=(⟨4,by decide⟩,⟨1,by decide⟩) := by decide +kernel

theorem meanFlatBasis_coordinates_7 (p : Fin 8) (b : Fin 2) :
    meanFlatBasis 7 (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) 7) := by
  rw [meanFlatBasis_apply,meanFlatIndex_eq_7,meanBasisColumnData_correct_7]
  change (√(meanScalarWeight (⟨4,by decide⟩:Fin 8)))⁻¹ *
    (if b=(⟨1,by decide⟩:Fin 2) then meanScalarRaw ⟨4,by decide⟩ p else 0)=_
  rw [meanNormalization_eq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;> fin_cases b <;>
    norm_num [meanTangentRaw,meanScalarRaw,meanNormalization,meanBasisColumnData_7,
      meanRadicalEval,angularCos,angularSin,layerSign,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

theorem meanBVertexKernel_data_7 (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex 7) p=meanRadicalEval (meanBKernelData 7 p) := by
  rw [meanFlatIndex_eq_7,meanBColumnData_correct_7]
  have hpart : meanPartner (⟨4,by decide⟩:Fin 8)=(⟨3,by decide⟩:Fin 8) := by decide +kernel
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases p <;>
    norm_num [meanBVertexKernel,meanScalarRaw,meanNormalization,meanBColumnData_7,meanRadicalEval,
      hpart,meanSinSign,meanBetaFactor,meanRadialFactor,angularCos,angularSin,layerSign,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,
      Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,div_eq_mul_inv,hi] <;>
    ring_nf <;> try simp only [hs] <;> ring_nf <;> try simp only [hs] <;> ring

#print axioms meanFlatBasis_coordinates_7
#print axioms meanBVertexKernel_data_7
end Blueprint.Thomson.Tail.Implementation
