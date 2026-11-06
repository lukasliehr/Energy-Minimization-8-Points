import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Invariant037
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0552.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3680 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/920 : ℚ)*Polynomial.X^2 + Polynomial.C (511/7360 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/115 : ℚ)*Polynomial.X^4 + Polynomial.C (-27103/7360 : ℚ)*Polynomial.X^5 + Polynomial.C (137717/3680 : ℚ)*Polynomial.X^6 + Polynomial.C (-719633/3680 : ℚ)*Polynomial.X^7 + Polynomial.C (298007/460 : ℚ)*Polynomial.X^8 + Polynomial.C (-525203/368 : ℚ)*Polynomial.X^9 + Polynomial.C (3812723/1840 : ℚ)*Polynomial.X^10 + Polynomial.C (-13620613/7360 : ℚ)*Polynomial.X^11 + Polynomial.C (91323/115 : ℚ)*Polynomial.X^12 + Polynomial.C (124357/1472 : ℚ)*Polynomial.X^13 + Polynomial.C (-150987/736 : ℚ)*Polynomial.X^14 + Polynomial.C (343/8 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf0540.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0540.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0540.rational a+Real.sqrt 2*evalQPoly rf0540.irrational a)/evalQPoly rf0540.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0540,rf0552]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (1/3680 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/736 : ℚ)*Polynomial.X^1 + Polynomial.C (429/7360 : ℚ)*Polynomial.X^2 + Polynomial.C (-277/7360 : ℚ)*Polynomial.X^3 + Polynomial.C (-4961/1472 : ℚ)*Polynomial.X^4 + Polynomial.C (238439/7360 : ℚ)*Polynomial.X^5 + Polynomial.C (-148661/920 : ℚ)*Polynomial.X^6 + Polynomial.C (1854167/3680 : ℚ)*Polynomial.X^7 + Polynomial.C (-931949/920 : ℚ)*Polynomial.X^8 + Polynomial.C (2306287/1840 : ℚ)*Polynomial.X^9 + Polynomial.C (-5674531/7360 : ℚ)*Polynomial.X^10 + Polynomial.C (-474313/7360 : ℚ)*Polynomial.X^11 + Polynomial.C (2638651/7360 : ℚ)*Polynomial.X^12 + Polynomial.C (-132493/1472 : ℚ)*Polynomial.X^13 + Polynomial.C (-197609/3680 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf0552.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0552.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0552.rational a+Real.sqrt 2*evalQPoly rf0552.irrational a)/evalQPoly rf0552.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0552,rf0552]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (1/3680 : ℚ)*Polynomial.X^0 + Polynomial.C (-47/7360 : ℚ)*Polynomial.X^1 + Polynomial.C (377/7360 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/7360 : ℚ)*Polynomial.X^3 + Polynomial.C (-22983/7360 : ℚ)*Polynomial.X^4 + Polynomial.C (51811/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (-503379/3680 : ℚ)*Polynomial.X^6 + Polynomial.C (13679/32 : ℚ)*Polynomial.X^7 + Polynomial.C (-1645603/1840 : ℚ)*Polynomial.X^8 + Polynomial.C (9046969/7360 : ℚ)*Polynomial.X^9 + Polynomial.C (-7422851/7360 : ℚ)*Polynomial.X^10 + Polynomial.C (2440937/7360 : ℚ)*Polynomial.X^11 + Polynomial.C (43687/320 : ℚ)*Polynomial.X^12 + Polynomial.C (-430291/3680 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf0564.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0564.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0564.rational a+Real.sqrt 2*evalQPoly rf0564.irrational a)/evalQPoly rf0564.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0564,rf0552]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/7360 : ℚ)*Polynomial.X^0 + Polynomial.C (21/7360 : ℚ)*Polynomial.X^1 + Polynomial.C (-129/7360 : ℚ)*Polynomial.X^2 + Polynomial.C (-409/7360 : ℚ)*Polynomial.X^3 + Polynomial.C (2731/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (-37407/3680 : ℚ)*Polynomial.X^5 + Polynomial.C (28291/736 : ℚ)*Polynomial.X^6 + Polynomial.C (-328441/3680 : ℚ)*Polynomial.X^7 + Polynomial.C (186427/1472 : ℚ)*Polynomial.X^8 + Polynomial.C (-721959/7360 : ℚ)*Polynomial.X^9 + Polynomial.C (156787/7360 : ℚ)*Polynomial.X^10 + Polynomial.C (159963/7360 : ℚ)*Polynomial.X^11 + Polynomial.C (-44273/3680 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf0576.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0576.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0576.rational a+Real.sqrt 2*evalQPoly rf0576.irrational a)/evalQPoly rf0576.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0576,rf0552]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (-1/7360 : ℚ)*Polynomial.X^0 + Polynomial.C (1/368 : ℚ)*Polynomial.X^1 + Polynomial.C (-113/7360 : ℚ)*Polynomial.X^2 + Polynomial.C (-49/736 : ℚ)*Polynomial.X^3 + Polynomial.C (5179/3680 : ℚ)*Polynomial.X^4 + Polynomial.C (-1615/184 : ℚ)*Polynomial.X^5 + Polynomial.C (110087/3680 : ℚ)*Polynomial.X^6 + Polynomial.C (-111637/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (520139/7360 : ℚ)*Polynomial.X^8 + Polynomial.C (-69107/1840 : ℚ)*Polynomial.X^9 + Polynomial.C (-27997/7360 : ℚ)*Polynomial.X^10 + Polynomial.C (36839/3680 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf0588.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0588.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0588.rational a+Real.sqrt 2*evalQPoly rf0588.irrational a)/evalQPoly rf0588.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0588,rf0552]
  all_goals ring

def vector (a : ℝ) : Fin 5 → ℝ := ![-rf0540.eval a,-rf0552.eval a,-rf0564.eval a,-rf0576.eval a,-rf0588.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0540.DefinedAt a) (h1 : rf0552.DefinedAt a) (h2 : rf0564.DefinedAt a) (h3 : rf0576.DefinedAt a) (h4 : rf0588.DefinedAt a) :
    ∀ r,∑ i,vector a i*(contactSigma a r)^i.val=orbitData a (invariantMonomial (0,3,1)) r := by
  intro r
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h1
  have hn : Real.sqrt 2≠0 := by positivity
  have hi : (Real.sqrt 2)⁻¹=Real.sqrt 2/2 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 := power_even_odd 2 (Real.sqrt 2) hs 3
  have hs4 := power_even_odd 2 (Real.sqrt 2) hs 4
  have hs5 := power_even_odd 2 (Real.sqrt 2) hs 5
  have hs6 := power_even_odd 2 (Real.sqrt 2) hs 6
  have hs7 := power_even_odd 2 (Real.sqrt 2) hs 7
  have hs8 := power_even_odd 2 (Real.sqrt 2) hs 8
  have hs9 := power_even_odd 2 (Real.sqrt 2) hs 9
  have hs10 := power_even_odd 2 (Real.sqrt 2) hs 10
  have hs11 := power_even_odd 2 (Real.sqrt 2) hs 11
  have hs12 := power_even_odd 2 (Real.sqrt 2) hs 12
  have hs13 := power_even_odd 2 (Real.sqrt 2) hs 13
  have hs14 := power_even_odd 2 (Real.sqrt 2) hs 14
  have hs15 := power_even_odd 2 (Real.sqrt 2) hs 15
  have hs16 := power_even_odd 2 (Real.sqrt 2) hs 16
  have hs17 := power_even_odd 2 (Real.sqrt 2) hs 17
  have hs18 := power_even_odd 2 (Real.sqrt 2) hs 18
  have hs19 := power_even_odd 2 (Real.sqrt 2) hs 19
  have hs20 := power_even_odd 2 (Real.sqrt 2) hs 20
  have hs21 := power_even_odd 2 (Real.sqrt 2) hs 21
  have hs22 := power_even_odd 2 (Real.sqrt 2) hs 22
  have hs23 := power_even_odd 2 (Real.sqrt 2) hs 23
  have hs24 := power_even_odd 2 (Real.sqrt 2) hs 24
  have hs25 := power_even_odd 2 (Real.sqrt 2) hs 25
  have hs26 := power_even_odd 2 (Real.sqrt 2) hs 26
  have hs27 := power_even_odd 2 (Real.sqrt 2) hs 27
  have hs28 := power_even_odd 2 (Real.sqrt 2) hs 28
  have hs29 := power_even_odd 2 (Real.sqrt 2) hs 29
  have hs30 := power_even_odd 2 (Real.sqrt 2) hs 30
  have hs31 := power_even_odd 2 (Real.sqrt 2) hs 31
  have hs32 := power_even_odd 2 (Real.sqrt 2) hs 32
  norm_num at hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27 hs28 hs29 hs30 hs31 hs32
  simp only [vector,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD]
  field_simp [hD]
  fin_cases r
  all_goals norm_num [evalQPoly,den,rf0552,n0,n1,n2,n3,n4,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0540.DefinedAt a) (h1 : rf0552.DefinedAt a) (h2 : rf0564.DefinedAt a) (h3 : rf0576.DefinedAt a) (h4 : rf0588.DefinedAt a) :
    invariantKernelCoefficients a (0,3,1)=vector a :=
  invariant_coefficients_unique a ha _ _ (values a ha h0 h1 h2 h3 h4)

#print axioms coefficients

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0540,rf0552,rf0013,rf0564,rf0013,rf0013,rf0576,rf0013,rf0013,rf0013,rf0588,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0),invariantMonomial (0,0,3),invariantMonomial (0,3,1),invariantMonomial (1,1,2),invariantMonomial (1,4,0),invariantMonomial (2,2,1),invariantMonomial (3,0,2),invariantMonomial (3,3,0),invariantMonomial (4,1,1),invariantMonomial (5,2,0),invariantMonomial (6,0,1),invariantMonomial (7,1,0),invariantMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0540.DefinedAt a) (h1 : rf0552.DefinedAt a) (h2 : rf0564.DefinedAt a) (h3 : rf0576.DefinedAt a) (h4 : rf0588.DefinedAt a) :
    rawColumn9 a=invariantKernelFeature a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Invariant037
