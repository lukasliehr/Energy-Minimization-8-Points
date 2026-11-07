import AllS.Units.N_GI.N_signed_mean.N_spectral_data
import AllS.Units.N_GI.N_contact_spectrum.N_block_positivity

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

/-- A strict margin below the manuscript's H bound, checked by its same
2-by-2 principal-minor calculation. -/
def meanHCeiling : ℝ := 412999/100000

theorem meanH_conditions (j : Fin 8) :
    0 < meanHCeiling-meanPhiEigen j ∧
    0 ≤ (meanHCeiling-meanPhiEigen j)*(meanHCeiling-meanMeridianEigen j)-
      (packingZHeight*meanBetaFactor j*meanSinSign j)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hlo : (141421356:ℝ)/10^8 < √2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ) < (141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hH := packing_parameters.2.2.1
  fin_cases j <;> constructor <;>
    norm_num [meanHCeiling,meanPhiEigen,meanMeridianEigen,meanBetaFactor,meanSinSign,mul_pow,hH,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3] <;> ring_nf <;> norm_num [hs,hs3] <;> nlinarith

theorem meanB_conditions (j : Fin 8) :
    packingRadius^2*((meanBetaFactor j*meanSinSign j)^2+
      (packingZHeight*meanRadialFactor j)^2) ≤ ((399:ℝ)/100)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hlo : (141421356:ℝ)/10^8 < √2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ) < (141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hH := packing_parameters.2.2.1
  have hR := packing_parameters.2.2.2
  fin_cases j <;>
    norm_num [meanBetaFactor,meanSinSign,meanRadialFactor,mul_pow,hH,hR,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3] <;> ring_nf <;> norm_num [hs,hs3] <;> nlinarith

theorem meanD_conditions (j : Fin 8) : 0 ≤ meanDEigen j ∧ meanDEigen j ≤ (2309:ℝ)/1000 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hlo : (141421356:ℝ)/10^8 < √2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ) < (141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  fin_cases j <;> norm_num [meanDEigen] <;> constructor <;> linarith

theorem meanH_block_bound (j : Fin 8) (x y : ℝ) :
    meanPhiEigen j*x^2+2*packingZHeight*meanBetaFactor j*meanSinSign j*x*y+
      meanMeridianEigen j*y^2 ≤ meanHCeiling*(x^2+y^2) := by
  obtain ⟨ha,hd⟩ := meanH_conditions j
  have h := contactBlock_psd (meanHCeiling-meanPhiEigen j) (meanHCeiling-meanMeridianEigen j)
    (-(packingZHeight*meanBetaFactor j*meanSinSign j)) x y ha (by simpa using hd)
  linarith

theorem meanB_block_bound (j : Fin 8) (x y : ℝ) :
    (packingRadius*(meanBetaFactor j*meanSinSign j*x+packingZHeight*meanRadialFactor j*y))^2 ≤
      ((399:ℝ)/100)^2*(x^2+y^2) := by
  have hcs : (meanBetaFactor j*meanSinSign j*x+packingZHeight*meanRadialFactor j*y)^2 ≤
      ((meanBetaFactor j*meanSinSign j)^2+(packingZHeight*meanRadialFactor j)^2)*(x^2+y^2) := by
    nlinarith [sq_nonneg (meanBetaFactor j*meanSinSign j*y-packingZHeight*meanRadialFactor j*x)]
  have h1 := mul_le_mul_of_nonneg_left hcs (sq_nonneg packingRadius)
  have h2 := mul_le_mul_of_nonneg_right (meanB_conditions j) (add_nonneg (sq_nonneg x) (sq_nonneg y))
  nlinarith

#print axioms meanH_conditions
#print axioms meanB_block_bound
#print axioms meanD_conditions
end Blueprint.Thomson.Tail.Implementation
