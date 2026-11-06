import AllS.Units.N_GI.N_signed_mean.N_spectral_data

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem meanD_raw (j k : Fin 8) :
    stressD (meanScalarRaw j) (meanScalarRaw k)=meanDEntry j k := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hs4 : (√(2:ℝ))^4=4 := by nlinarith [sq_nonneg ((√(2:ℝ))^2-2)]
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  unfold stressD
  fin_cases j <;> fin_cases k <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,meanScalarRaw,
      contactWeight,contactNext,boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,angularCos,angularSin,layerSign,
      meanDEntry,meanScalarWeight,meanDEigen,packingHeight,
      contactKappa_formula,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hs,hs3,hs4] <;> ring_nf <;> simp [hs,hs3,hs4] <;> ring

#print axioms meanD_raw
end Blueprint.Thomson.Tail.Implementation
