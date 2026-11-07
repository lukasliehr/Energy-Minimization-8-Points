import AllS.Units.N_GI.N_contact_spectrum.N_gram_data

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contactGram_raw_row_4 (w : ℝ) (k : Fin 13) :
    contactGram w (contactRawVector 4) (contactRawVector k)=contactGramEntry w 4 k := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hs4 : (√(2:ℝ))^4=4 := by nlinarith [sq_nonneg ((√(2:ℝ))^2-2)]
  have hs5 : (√(2:ℝ))^5=4*√2 := by rw [pow_succ,hs4]
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  have hH := packing_parameters.2.2.1
  unfold contactGram
  simp_rw [contactLinear_cyclic_formula]
  fin_cases k <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,contactRawVector,boundaryRaw,
      boundaryRawPair,boundaryBasisIndex,contactNext,contactSine,contactMeridianFactor,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,angularCos,angularSin,layerSign,
      contactGramEntry,contactGramDiagonal,contactGramMixed1,contactGramMixed2,
      contactKappa_formula,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hH,packingHeight,hs,hs3,hs4,hs5] <;>
    ring_nf <;> simp [hs,hs3,hs4,hs5] <;> ring

#print axioms contactGram_raw_row_4
end Blueprint.Thomson.Tail.Implementation
