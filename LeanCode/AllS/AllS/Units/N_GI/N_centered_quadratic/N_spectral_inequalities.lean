import AllS.Units.N_GI.N_centered_quadratic.N_spectral_data
import AllS.Units.N_GI.N_contact_spectrum.N_block_positivity

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem centeredQ_conditions (j : Fin 8) :
    0 < 4-centeredPhiEigen j ∧
    0 ≤ (4-centeredPhiEigen j)*(4-centeredMeridianEigen j)-
      (packingZHeight*centeredBetaFactor j*meanSinSign j)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hlo : (141421356:ℝ)/10^8 < √2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ) < (141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hH := packing_parameters.2.2.1
  fin_cases j <;> constructor <;>
    norm_num [centeredPhiEigen,centeredMeridianEigen,centeredBetaFactor,meanSinSign,mul_pow,hH,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3] <;> ring_nf <;> norm_num [hs,hs3] <;> nlinarith

theorem centeredQ_block_bound (j : Fin 8) (x y : ℝ) :
    centeredPhiEigen j*x^2+2*packingZHeight*centeredBetaFactor j*meanSinSign j*x*y+
      centeredMeridianEigen j*y^2 ≤ 4*(x^2+y^2) := by
  obtain ⟨ha,hd⟩ := centeredQ_conditions j
  have h := contactBlock_psd (4-centeredPhiEigen j) (4-centeredMeridianEigen j)
    (-(packingZHeight*centeredBetaFactor j*meanSinSign j)) x y ha (by simpa using hd)
  linarith

#print axioms centeredQ_block_bound
end Blueprint.Thomson.Tail.Implementation
