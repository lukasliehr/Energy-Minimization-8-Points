import Blueprint.TailLocalCoordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem packing_parameters : 0 < packingZHeight ∧ 0 < packingRadius ∧
    packingZHeight^2=packingHeight ∧ packingRadius^2=1-packingHeight := by
  have ha : packingHeight ∈ Set.Ioo (0:ℝ) 1 := SquareAntiprismVerification.aInf_mem_Ioo
  exact ⟨Real.sqrt_pos.mpr ha.1,Real.sqrt_pos.mpr (by linarith [ha.2]),
    Real.sq_sqrt ha.1.le,Real.sq_sqrt (by linarith [ha.2])⟩

theorem angular_unit (i : Fin 8) : (angularCos i)^2+(angularSin i)^2=1 ∧ (layerSign i)^2=1 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> norm_num [angularCos,angularSin,layerSign,div_pow,hs]

theorem packingReference_formula (i : Fin 8) : packingReference i=
    !₂[packingRadius*angularCos i,packingRadius*angularSin i,layerSign i*packingZHeight] := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [packingReference,cyclicIndex,X,packingRadius,packingZHeight,angularCos,angularSin,layerSign] <;> ring

def localFrame (i : Fin 8) : Fin 3 → Point := ![packingReference i,azimuthFrame i,meridianFrame i]

theorem localFrame_orthonormal (i : Fin 8) : Orthonormal ℝ (localFrame i) := by
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  obtain ⟨hc,he⟩ := angular_unit i
  have hsum : packingZHeight^2+packingRadius^2=1 := by linarith
  have hPP : inner ℝ (packingReference i) (packingReference i)=1 := by
    rw [packingReference_formula,PiLp.inner_apply]
    simp [Fin.sum_univ_succ]
    linear_combination packingRadius^2*hc+packingZHeight^2*he+hsum
  have hff : inner ℝ (azimuthFrame i) (azimuthFrame i)=1 := by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ,azimuthFrame]
    nlinarith
  have hgg : inner ℝ (meridianFrame i) (meridianFrame i)=1 := by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ,meridianFrame]
    linear_combination packingZHeight^2*hc+packingRadius^2*he+hsum
  have hPf : inner ℝ (packingReference i) (azimuthFrame i)=0 := by
    rw [packingReference_formula,PiLp.inner_apply]
    simp [azimuthFrame,Fin.sum_univ_succ]
    ring
  have hPg : inner ℝ (packingReference i) (meridianFrame i)=0 := by
    rw [packingReference_formula,PiLp.inner_apply]
    simp [Fin.sum_univ_succ,meridianFrame]
    linear_combination packingRadius*packingZHeight*(he-hc)
  have hfg : inner ℝ (azimuthFrame i) (meridianFrame i)=0 := by
    rw [PiLp.inner_apply]
    simp [azimuthFrame,meridianFrame,Fin.sum_univ_succ]
    ring
  have hfP : inner ℝ (azimuthFrame i) (packingReference i)=0 := by rw [real_inner_comm]; exact hPf
  have hgP : inner ℝ (meridianFrame i) (packingReference i)=0 := by rw [real_inner_comm]; exact hPg
  have hgf : inner ℝ (meridianFrame i) (azimuthFrame i)=0 := by rw [real_inner_comm]; exact hfg
  rw [orthonormal_iff_ite]
  intro j k
  fin_cases j <;> fin_cases k <;> dsimp [localFrame] <;>
    simp only [hPP,hff,hgg,hPf,hPg,hfg,hfP,hgP,hgf] <;> norm_num

#print axioms localFrame_orthonormal
end Blueprint.Thomson.Tail.Implementation
