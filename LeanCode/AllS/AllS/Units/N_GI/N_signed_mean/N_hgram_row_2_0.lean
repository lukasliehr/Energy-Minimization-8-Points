import AllS.Units.N_GI.N_signed_mean.N_spectral_data

set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem meanH_raw_row_2_0 (k : Fin 8 × Fin 2) :
    stressH (meanTangentRaw (2,0)) (meanTangentRaw k)=meanHEntry (2,0) k := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hs4 : (√(2:ℝ))^4=4 := by nlinarith [sq_nonneg ((√(2:ℝ))^2-2)]
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  rw [stressH_coordinate_formula]
  rcases k with ⟨j,c⟩
  fin_cases j <;> fin_cases c <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,meanTangentRaw,meanScalarRaw,
      contactFrameDot,contactWeight,contactNext,contactCosine,contactSine,contactParity,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,angularCos,angularSin,layerSign,
      meanHEntry,meanScalarWeight,meanPartner,meanSinSign,meanBetaFactor,meanPhiEigen,meanMeridianEigen,
      contactKappa_formula,div_eq_mul_inv,hinv,packingHeight] <;>
    ring_nf <;> simp [hs,hs3,hs4] <;> ring_nf <;> simp [hs,hs3,hs4] <;> ring

#print axioms meanH_raw_row_2_0
end Blueprint.Thomson.Tail.Implementation
