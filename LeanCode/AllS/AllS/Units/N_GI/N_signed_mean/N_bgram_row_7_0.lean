import AllS.Units.N_GI.N_signed_mean.N_spectral_data

set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem meanB_raw_row_7_0 (k : Fin 8) :
    stressB (meanTangentRaw (7,0)) (meanScalarRaw k)=meanBEntry (7,0) k := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  rw [stressB_coordinate_formula]
  fin_cases k <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,meanTangentRaw,meanScalarRaw,
      contactWeight,contactNext,contactSine,contactMeridianFactor,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,angularCos,angularSin,layerSign,
      meanBEntry,meanScalarWeight,meanPartner,meanSinSign,meanBetaFactor,meanRadialFactor,
      contactKappa_formula,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hs,hs3] <;> ring_nf <;> simp [hs,hs3] <;> ring

#print axioms meanB_raw_row_7_0
end Blueprint.Thomson.Tail.Implementation
