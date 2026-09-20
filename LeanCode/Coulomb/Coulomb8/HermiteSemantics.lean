import Coulomb8.HermiteModel

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace Coulomb8
namespace HermiteArithmetic
open Polynomial

theorem taylor_eval0 : v81=taylor4.eval (nodes a 0) := by
  rw [eval_p0_v0,RealPoly.eval,taylor_model]
  rfl
theorem taylor_derivative_eval0 : v92=taylor4.derivative.eval (nodes a 0) := by
  rw [eval_p1_v0,RealPoly.eval,p1_eq,RealPoly.toPolynomial_derivative,taylor_model]
  rfl
theorem lagrange_derivative_eval0 : v110=(lagrange 0).derivative.eval (nodes a 0) := by
  rw [eval_p12_v0,RealPoly.eval,p12_eq,RealPoly.toPolynomial_derivative,lagrange_model0]
  rfl

theorem value_model0 : v85=residualValue 0 := by
  norm_num [v13,v15,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v82,v83,v84,v85,v0,taylor_eval0,residualValue,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem slope_model0 : v102=residualSlope 0 := by
  norm_num [v13,v15,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v84,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v0,taylor_derivative_eval0,value_model0,residualSlope,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem term_model0 : p18.toPolynomial=hermiteTerm 0 := by
  simp only [p12_eq,p15_eq,p16_eq,p17_eq,p18_eq,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale,RealPoly.toPolynomial_add,lagrange_model0]
  norm_num [p13,p14,p15,p16,p17,p18,v13,v15,v111,v112,v113,v114,v115,v116,v117,v118,v0,value_model0,slope_model0,lagrange_derivative_eval0,RealPoly.toPolynomial,hermiteTerm]
  <;> ring <;> rfl

theorem taylor_eval1 : v225=taylor4.eval (nodes a 1) := by
  rw [eval_p0_v1,RealPoly.eval,taylor_model]
  rfl
theorem taylor_derivative_eval1 : v236=taylor4.derivative.eval (nodes a 1) := by
  rw [eval_p1_v1,RealPoly.eval,p1_eq,RealPoly.toPolynomial_derivative,taylor_model]
  rfl
theorem lagrange_derivative_eval1 : v253=(lagrange 1).derivative.eval (nodes a 1) := by
  rw [eval_p29_v1,RealPoly.eval,p29_eq,RealPoly.toPolynomial_derivative,lagrange_model1]
  rfl

theorem value_model1 : v229=residualValue 1 := by
  norm_num [v13,v15,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v226,v227,v228,v229,v1,taylor_eval1,residualValue,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem slope_model1 : v245=residualSlope 1 := by
  norm_num [v13,v15,v97,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v228,v237,v238,v239,v240,v241,v242,v243,v244,v245,v1,taylor_derivative_eval1,value_model1,residualSlope,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem term_model1 : p35.toPolynomial=hermiteTerm 1 := by
  simp only [p29_eq,p32_eq,p33_eq,p34_eq,p35_eq,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale,RealPoly.toPolynomial_add,lagrange_model1]
  norm_num [p30,p31,p32,p33,p34,p35,v13,v15,v21,v254,v255,v256,v257,v258,v259,v260,v1,value_model1,slope_model1,lagrange_derivative_eval1,RealPoly.toPolynomial,hermiteTerm]
  <;> ring <;> rfl

theorem taylor_eval2 : v365=taylor4.eval (nodes a 2) := by
  rw [eval_p0_v2,RealPoly.eval,taylor_model]
  rfl
theorem taylor_derivative_eval2 : v376=taylor4.derivative.eval (nodes a 2) := by
  rw [eval_p1_v2,RealPoly.eval,p1_eq,RealPoly.toPolynomial_derivative,taylor_model]
  rfl
theorem lagrange_derivative_eval2 : v393=(lagrange 2).derivative.eval (nodes a 2) := by
  rw [eval_p46_v2,RealPoly.eval,p46_eq,RealPoly.toPolynomial_derivative,lagrange_model2]
  rfl

theorem value_model2 : v369=residualValue 2 := by
  norm_num [v13,v15,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v366,v367,v368,v369,v2,taylor_eval2,residualValue,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem slope_model2 : v385=residualSlope 2 := by
  norm_num [v13,v15,v97,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v368,v377,v378,v379,v380,v381,v382,v383,v384,v385,v2,taylor_derivative_eval2,value_model2,residualSlope,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem term_model2 : p52.toPolynomial=hermiteTerm 2 := by
  simp only [p46_eq,p49_eq,p50_eq,p51_eq,p52_eq,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale,RealPoly.toPolynomial_add,lagrange_model2]
  norm_num [p47,p48,p49,p50,p51,p52,v13,v15,v30,v394,v395,v396,v397,v398,v399,v400,v2,value_model2,slope_model2,lagrange_derivative_eval2,RealPoly.toPolynomial,hermiteTerm]
  <;> ring <;> rfl

theorem taylor_eval3 : v505=taylor4.eval (nodes a 3) := by
  rw [eval_p0_v3,RealPoly.eval,taylor_model]
  rfl
theorem taylor_derivative_eval3 : v516=taylor4.derivative.eval (nodes a 3) := by
  rw [eval_p1_v3,RealPoly.eval,p1_eq,RealPoly.toPolynomial_derivative,taylor_model]
  rfl
theorem lagrange_derivative_eval3 : v533=(lagrange 3).derivative.eval (nodes a 3) := by
  rw [eval_p63_v3,RealPoly.eval,p63_eq,RealPoly.toPolynomial_derivative,lagrange_model3]
  rfl

theorem value_model3 : v509=residualValue 3 := by
  norm_num [v13,v15,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v506,v507,v508,v509,v3,taylor_eval3,residualValue,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem slope_model3 : v525=residualSlope 3 := by
  norm_num [v13,v15,v97,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v508,v517,v518,v519,v520,v521,v522,v523,v524,v525,v3,taylor_derivative_eval3,value_model3,residualSlope,phi,div_eq_mul_inv,← inv_pow] <;> ring_nf

theorem term_model3 : p69.toPolynomial=hermiteTerm 3 := by
  simp only [p63_eq,p66_eq,p67_eq,p68_eq,p69_eq,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale,RealPoly.toPolynomial_add,lagrange_model3]
  norm_num [p64,p65,p66,p67,p68,p69,v13,v15,v43,v534,v535,v536,v537,v538,v539,v540,v3,value_model3,slope_model3,lagrange_derivative_eval3,RealPoly.toPolynomial,hermiteTerm]
  <;> ring <;> rfl

theorem residual_model : p74.toPolynomial=residualPolynomial := by
  simp only [p71_eq,p72_eq,p73_eq,p74_eq,RealPoly.toPolynomial_add,term_model0,term_model1,term_model2,term_model3]
  norm_num [residualPolynomial,Fin.sum_univ_succ,Fin.succ,p70,RealPoly.toPolynomial,v26]
  <;> ring <;> rfl
theorem power_model : p75.toPolynomial=(X+1)^5 := by
  apply Polynomial.funext
  intro x
  norm_num [p75,RealPoly.toPolynomial,v13,v97,v617,v617,v97,v13] <;> ring
theorem hermite_model : p77.toPolynomial=Hpoly := by
  rw [p77_eq,RealPoly.toPolynomial_add,p76_eq,RealPoly.toPolynomial_mul,taylor_model,power_model,residual_model]
  rfl

end HermiteArithmetic
end Coulomb8

#print axioms Coulomb8.HermiteArithmetic.hermite_model
