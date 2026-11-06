import AllS.Units.N_GI.N_contact_spectrum.N_gram_data

set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def ContactSpectrumConditions (w L : ℝ) : Prop :=
  8*L ≤ contactGramDiagonal w 0 ∧
  4*(1+packingHeight)*L ≤ contactGramDiagonal w 9 ∧
  8*L ≤ contactGramDiagonal w 11 ∧
  8*L ≤ contactGramDiagonal w 12 ∧
  0 < contactGramDiagonal w 1-4*L ∧
  0 ≤ (contactGramDiagonal w 1-4*L)*(contactGramDiagonal w 3-4*L)-(contactGramMixed1 w)^2 ∧
  0 < contactGramDiagonal w 5-4*L ∧
  0 ≤ (contactGramDiagonal w 5-4*L)*(contactGramDiagonal w 7-4*L)-contactGramMixed2^2

theorem contactBlock_psd (A D B x y : ℝ) (hA : 0<A) (hdet : 0≤A*D-B^2) :
    0≤A*x^2+2*B*x*y+D*y^2 := by
  have h := mul_nonneg hdet (sq_nonneg y)
  have hs := sq_nonneg (A*x+B*y)
  nlinarith

theorem contactBlock_lower (a d b L x y : ℝ) (hA : 0<a-4*L)
    (hdet : 0≤(a-4*L)*(d-4*L)-b^2) :
    L*(4*x^2+4*y^2) ≤ a*x^2+2*b*x*y+d*y^2 := by
  have h := contactBlock_psd (a-4*L) (d-4*L) b x y hA hdet
  nlinarith

theorem contact_spectrum_weighted_conditions : ContactSpectrumConditions contactKappa (59546/15625) := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hs4 : (√(2:ℝ))^4=4 := by nlinarith [sq_nonneg ((√(2:ℝ))^2-2)]
  have hs5 : (√(2:ℝ))^5=4*√2 := by rw [pow_succ,hs4]
  have hlo : (141421356:ℝ)/10^8<√2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ)<(141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hH := packing_parameters.2.2.1
  have hR := packing_parameters.2.2.2
  unfold ContactSpectrumConditions
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp [contactGramDiagonal]
  all_goals
    norm_num [contactGramDiagonal,contactGramMixed1,contactGramMixed2,contactKappa_formula,
      mul_pow,div_pow,hs,hH,hR,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3,hs4,hs5,hH,hR,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3,hs4,hs5] <;> nlinarith

theorem contact_spectrum_unweighted_conditions : ContactSpectrumConditions 1 3 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  have hs4 : (√(2:ℝ))^4=4 := by nlinarith [sq_nonneg ((√(2:ℝ))^2-2)]
  have hs5 : (√(2:ℝ))^5=4*√2 := by rw [pow_succ,hs4]
  have hlo : (141421356:ℝ)/10^8<√2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ)<(141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hH := packing_parameters.2.2.1
  have hR := packing_parameters.2.2.2
  unfold ContactSpectrumConditions
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp [contactGramDiagonal]
  all_goals
    norm_num [contactGramDiagonal,contactGramMixed1,contactGramMixed2,contactKappa_formula,
      mul_pow,div_pow,hs,hH,hR,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3,hs4,hs5,hH,hR,packingHeight] <;>
    ring_nf <;> norm_num [hs,hs3,hs4,hs5] <;> nlinarith

#print axioms contact_spectrum_weighted_conditions
#print axioms contact_spectrum_unweighted_conditions
end Blueprint.Thomson.Tail.Implementation
