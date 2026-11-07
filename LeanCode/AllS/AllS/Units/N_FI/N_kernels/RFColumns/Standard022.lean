import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Standard022
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0316.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (7/80 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^3 + Polynomial.C (873/80 : ℚ)*Polynomial.X^4 + Polynomial.C (-1729/40 : ℚ)*Polynomial.X^5 + Polynomial.C (7737/80 : ℚ)*Polynomial.X^6 + Polynomial.C (-445/4 : ℚ)*Polynomial.X^7 + Polynomial.C (3063/80 : ℚ)*Polynomial.X^8 + Polynomial.C (195/8 : ℚ)*Polynomial.X^9 + Polynomial.C (-8/5 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf0292.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0292.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0292.rational a+Real.sqrt 2*evalQPoly rf0292.irrational a)/evalQPoly rf0292.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0292,rf0316]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (11/120 : ℚ)*Polynomial.X^1 + Polynomial.C (-383/240 : ℚ)*Polynomial.X^2 + Polynomial.C (1367/120 : ℚ)*Polynomial.X^3 + Polynomial.C (-10061/240 : ℚ)*Polynomial.X^4 + Polynomial.C (157/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-12161/240 : ℚ)*Polynomial.X^6 + Polynomial.C (-5249/120 : ℚ)*Polynomial.X^7 + Polynomial.C (2465/48 : ℚ)*Polynomial.X^8 + Polynomial.C (641/40 : ℚ)*Polynomial.X^9 + Polynomial.C (19/10 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf0304.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0304.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0304.rational a+Real.sqrt 2*evalQPoly rf0304.irrational a)/evalQPoly rf0304.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0304,rf0316]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/24 : ℚ)*Polynomial.X^1 + Polynomial.C (-49/240 : ℚ)*Polynomial.X^2 + Polynomial.C (281/60 : ℚ)*Polynomial.X^3 + Polynomial.C (-6437/240 : ℚ)*Polynomial.X^4 + Polynomial.C (1711/24 : ℚ)*Polynomial.X^5 + Polynomial.C (-6701/80 : ℚ)*Polynomial.X^6 + Polynomial.C (102/5 : ℚ)*Polynomial.X^7 + Polynomial.C (1087/60 : ℚ)*Polynomial.X^8 + Polynomial.C (3/5 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf0316.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0316.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0316.rational a+Real.sqrt 2*evalQPoly rf0316.irrational a)/evalQPoly rf0316.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0316,rf0316]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/12 : ℚ)*Polynomial.X^1 + Polynomial.C (139/240 : ℚ)*Polynomial.X^2 + Polynomial.C (-193/120 : ℚ)*Polynomial.X^3 + Polynomial.C (33/80 : ℚ)*Polynomial.X^4 + Polynomial.C (97/15 : ℚ)*Polynomial.X^5 + Polynomial.C (-2059/240 : ℚ)*Polynomial.X^6 + Polynomial.C (-109/120 : ℚ)*Polynomial.X^7 + Polynomial.C (-11/20 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf0328.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0328.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0328.rational a+Real.sqrt 2*evalQPoly rf0328.irrational a)/evalQPoly rf0328.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0328,rf0316]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/40 : ℚ)*Polynomial.X^3 + Polynomial.C (269/20 : ℚ)*Polynomial.X^4 + Polynomial.C (-2349/40 : ℚ)*Polynomial.X^5 + Polynomial.C (1069/10 : ℚ)*Polynomial.X^6 + Polynomial.C (-2323/40 : ℚ)*Polynomial.X^7 + Polynomial.C (-499/20 : ℚ)*Polynomial.X^8 + Polynomial.C (-33/10 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf0340.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0340.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0340.rational a+Real.sqrt 2*evalQPoly rf0340.irrational a)/evalQPoly rf0340.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0340,rf0316]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/40 : ℚ)*Polynomial.X^2 + Polynomial.C (509/40 : ℚ)*Polynomial.X^3 + Polynomial.C (-1811/40 : ℚ)*Polynomial.X^4 + Polynomial.C (1927/40 : ℚ)*Polynomial.X^5 + Polynomial.C (1953/40 : ℚ)*Polynomial.X^6 + Polynomial.C (-3321/40 : ℚ)*Polynomial.X^7 + Polynomial.C (-113/4 : ℚ)*Polynomial.X^8 + Polynomial.C (-33/10 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf0352.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0352.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0352.rational a+Real.sqrt 2*evalQPoly rf0352.irrational a)/evalQPoly rf0352.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0352,rf0316]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/40 : ℚ)*Polynomial.X^2 + Polynomial.C (269/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-2349/40 : ℚ)*Polynomial.X^4 + Polynomial.C (1069/10 : ℚ)*Polynomial.X^5 + Polynomial.C (-2323/40 : ℚ)*Polynomial.X^6 + Polynomial.C (-499/20 : ℚ)*Polynomial.X^7 + Polynomial.C (-33/10 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf0364.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0364.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0364.rational a+Real.sqrt 2*evalQPoly rf0364.irrational a)/evalQPoly rf0364.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0364,rf0316]
  all_goals ring

def vectorF (a : ℝ) : Fin 4 → ℝ := ![-rf0292.eval a,-rf0304.eval a,-rf0316.eval a,-rf0328.eval a]
def vectorG (a : ℝ) : Fin 3 → ℝ := ![-rf0340.eval a,-rf0352.eval a,-rf0364.eval a]
theorem regular_values (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    ∀ r : Fin 2,(∑ i,vectorF a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputF (false,1,1,1)) (regularOrbit r) ∧ (∑ i,vectorG a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputG (false,1,1,1)) (regularOrbit r) := by
  intro r
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h2
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
  constructor
  all_goals simp only [vectorF,vectorG,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD]
  all_goals field_simp [hD]
  all_goals fin_cases r
  all_goals norm_num [evalQPoly,den,rf0316,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem repeated_values (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    ∀ r : Fin 3,(∑ i,vectorF a i*contactSigma a (Fin.castAdd 2 r)^i.val)+repeatedLambda a r*(∑ i,vectorG a i*contactSigma a (Fin.castAdd 2 r)^i.val)=orbitData a (standardInputF (false,1,1,1)) (Fin.castAdd 2 r)+repeatedLambda a r*orbitData a (standardInputG (false,1,1,1)) (Fin.castAdd 2 r) := by
  intro r
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h2
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
  all_goals simp only [vectorF,vectorG,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD]
  all_goals field_simp [hD]
  all_goals fin_cases r
  all_goals norm_num [evalQPoly,den,rf0316,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    standardKernelFCoefficients a (false,1,1,1)=vectorF a ∧ standardKernelGCoefficients a (false,1,1,1)=vectorG a :=
  standard_coefficients_unique a ha _ _ _ (regular_values a ha h0 h1 h2 h3 h4 h5 h6) (repeated_values a ha h0 h1 h2 h3 h4 h5 h6)

#print axioms coefficients

def rawColumn7 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0292,rf0304,rf0013,rf0316,rf0013,rf0013,rf0328,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0340,rf0352,rf0013,rf0364,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0)]

theorem raw_column_7 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    rawColumn7 minus a=standardKernelFeature minus a (false,1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0292,rf0304,rf0013,rf0316,rf0013,rf0013,rf0328,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0340,rf0352,rf0013,rf0364,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (false,0,2,1),standardRawFeature minus (false,1,0,2),standardRawFeature minus (false,1,3,0),standardRawFeature minus (false,2,1,1),standardRawFeature minus (false,3,2,0),standardRawFeature minus (false,4,0,1),standardRawFeature minus (false,5,1,0),standardRawFeature minus (false,7,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0),standardRawFeature minus (true,0,0,2),standardRawFeature minus (true,0,3,0),standardRawFeature minus (true,1,1,1),standardRawFeature minus (true,2,2,0),standardRawFeature minus (true,3,0,1),standardRawFeature minus (true,4,1,0),standardRawFeature minus (true,6,0,0)]

theorem raw_column_8 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    rawColumn8 minus a=standardKernelFeature minus a (false,1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0292,rf0304,rf0013,rf0316,rf0013,rf0013,rf0328,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0340,rf0352,rf0013,rf0364,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (false,0,2,1),standardRawFeature minus (false,1,0,2),standardRawFeature minus (false,1,3,0),standardRawFeature minus (false,2,1,1),standardRawFeature minus (false,3,2,0),standardRawFeature minus (false,4,0,1),standardRawFeature minus (false,5,1,0),standardRawFeature minus (false,7,0,0),standardRawFeature minus (false,0,1,2),standardRawFeature minus (false,0,4,0),standardRawFeature minus (false,1,2,1),standardRawFeature minus (false,2,0,2),standardRawFeature minus (false,2,3,0),standardRawFeature minus (false,3,1,1),standardRawFeature minus (false,4,2,0),standardRawFeature minus (false,5,0,1),standardRawFeature minus (false,6,1,0),standardRawFeature minus (false,8,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0),standardRawFeature minus (true,0,0,2),standardRawFeature minus (true,0,3,0),standardRawFeature minus (true,1,1,1),standardRawFeature minus (true,2,2,0),standardRawFeature minus (true,3,0,1),standardRawFeature minus (true,4,1,0),standardRawFeature minus (true,6,0,0),standardRawFeature minus (true,0,2,1),standardRawFeature minus (true,1,0,2),standardRawFeature minus (true,1,3,0),standardRawFeature minus (true,2,1,1),standardRawFeature minus (true,3,2,0),standardRawFeature minus (true,4,0,1),standardRawFeature minus (true,5,1,0),standardRawFeature minus (true,7,0,0)]

theorem raw_column_9 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0292.DefinedAt a) (h1 : rf0304.DefinedAt a) (h2 : rf0316.DefinedAt a) (h3 : rf0328.DefinedAt a) (h4 : rf0340.DefinedAt a) (h5 : rf0352.DefinedAt a) (h6 : rf0364.DefinedAt a) :
    rawColumn9 minus a=standardKernelFeature minus a (false,1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Standard022
