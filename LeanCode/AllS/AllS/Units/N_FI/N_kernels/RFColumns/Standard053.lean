import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Standard053
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0655.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/80 : ℚ)*Polynomial.X^2 + Polynomial.C (41/40 : ℚ)*Polynomial.X^3 + Polynomial.C (-19/80 : ℚ)*Polynomial.X^4 + Polynomial.C (-587/20 : ℚ)*Polynomial.X^5 + Polynomial.C (12649/80 : ℚ)*Polynomial.X^6 + Polynomial.C (-18373/40 : ℚ)*Polynomial.X^7 + Polynomial.C (15639/16 : ℚ)*Polynomial.X^8 + Polynomial.C (-8216/5 : ℚ)*Polynomial.X^9 + Polynomial.C (18997/10 : ℚ)*Polynomial.X^10 + Polynomial.C (-24199/20 : ℚ)*Polynomial.X^11 + Polynomial.C (3187/10 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf0619.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0619.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0619.rational a+Real.sqrt 2*evalQPoly rf0619.irrational a)/evalQPoly rf0619.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0619,rf0655]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/120 : ℚ)*Polynomial.X^1 + Polynomial.C (37/48 : ℚ)*Polynomial.X^2 + Polynomial.C (161/60 : ℚ)*Polynomial.X^3 + Polynomial.C (-3243/80 : ℚ)*Polynomial.X^4 + Polynomial.C (18343/120 : ℚ)*Polynomial.X^5 + Polynomial.C (-22691/80 : ℚ)*Polynomial.X^6 + Polynomial.C (1557/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-13181/80 : ℚ)*Polynomial.X^8 + Polynomial.C (-11357/30 : ℚ)*Polynomial.X^9 + Polynomial.C (16534/15 : ℚ)*Polynomial.X^10 + Polynomial.C (-14996/15 : ℚ)*Polynomial.X^11 + Polynomial.C (3187/10 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf0637.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0637.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0637.rational a+Real.sqrt 2*evalQPoly rf0637.irrational a)/evalQPoly rf0637.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0637,rf0655]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^1 + Polynomial.C (679/240 : ℚ)*Polynomial.X^2 + Polynomial.C (-247/24 : ℚ)*Polynomial.X^3 + Polynomial.C (-2017/240 : ℚ)*Polynomial.X^4 + Polynomial.C (10127/60 : ℚ)*Polynomial.X^5 + Polynomial.C (-9273/16 : ℚ)*Polynomial.X^6 + Polynomial.C (47389/40 : ℚ)*Polynomial.X^7 + Polynomial.C (-25756/15 : ℚ)*Polynomial.X^8 + Polynomial.C (33139/20 : ℚ)*Polynomial.X^9 + Polynomial.C (-2711/3 : ℚ)*Polynomial.X^10 + Polynomial.C (12613/60 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf0655.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0655.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0655.rational a+Real.sqrt 2*evalQPoly rf0655.irrational a)/evalQPoly rf0655.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0655,rf0655]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/120 : ℚ)*Polynomial.X^1 + Polynomial.C (227/240 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^3 + Polynomial.C (-937/240 : ℚ)*Polynomial.X^4 + Polynomial.C (3099/40 : ℚ)*Polynomial.X^5 + Polynomial.C (-22081/80 : ℚ)*Polynomial.X^6 + Polynomial.C (2689/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-9526/15 : ℚ)*Polynomial.X^8 + Polynomial.C (12137/30 : ℚ)*Polynomial.X^9 + Polynomial.C (-3187/30 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf0673.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0673.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0673.rational a+Real.sqrt 2*evalQPoly rf0673.irrational a)/evalQPoly rf0673.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0673,rf0655]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-17/20 : ℚ)*Polynomial.X^2 + Polynomial.C (239/40 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-1109/8 : ℚ)*Polynomial.X^5 + Polynomial.C (13581/20 : ℚ)*Polynomial.X^6 + Polynomial.C (-71931/40 : ℚ)*Polynomial.X^7 + Polynomial.C (16128/5 : ℚ)*Polynomial.X^8 + Polynomial.C (-18854/5 : ℚ)*Polynomial.X^9 + Polynomial.C (24091/10 : ℚ)*Polynomial.X^10 + Polynomial.C (-6359/10 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf0691.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0691.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0691.rational a+Real.sqrt 2*evalQPoly rf0691.irrational a)/evalQPoly rf0691.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0691,rf0655]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (-33/40 : ℚ)*Polynomial.X^1 + Polynomial.C (41/8 : ℚ)*Polynomial.X^2 + Polynomial.C (203/40 : ℚ)*Polynomial.X^3 + Polynomial.C (-5581/40 : ℚ)*Polynomial.X^4 + Polynomial.C (21617/40 : ℚ)*Polynomial.X^5 + Polynomial.C (-44769/40 : ℚ)*Polynomial.X^6 + Polynomial.C (57093/40 : ℚ)*Polynomial.X^7 + Polynomial.C (-2726/5 : ℚ)*Polynomial.X^8 + Polynomial.C (-13617/10 : ℚ)*Polynomial.X^9 + Polynomial.C (8866/5 : ℚ)*Polynomial.X^10 + Polynomial.C (-6359/10 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf0709.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0709.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0709.rational a+Real.sqrt 2*evalQPoly rf0709.irrational a)/evalQPoly rf0709.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0709,rf0655]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/20 : ℚ)*Polynomial.X^1 + Polynomial.C (239/40 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-1109/8 : ℚ)*Polynomial.X^4 + Polynomial.C (13581/20 : ℚ)*Polynomial.X^5 + Polynomial.C (-71931/40 : ℚ)*Polynomial.X^6 + Polynomial.C (16128/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-18854/5 : ℚ)*Polynomial.X^8 + Polynomial.C (24091/10 : ℚ)*Polynomial.X^9 + Polynomial.C (-6359/10 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf0727.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0727.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0727.rational a+Real.sqrt 2*evalQPoly rf0727.irrational a)/evalQPoly rf0727.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0727,rf0655]
  all_goals ring

def vectorF (a : ℝ) : Fin 4 → ℝ := ![-rf0619.eval a,-rf0637.eval a,-rf0655.eval a,-rf0673.eval a]
def vectorG (a : ℝ) : Fin 3 → ℝ := ![-rf0691.eval a,-rf0709.eval a,-rf0727.eval a]
theorem regular_values (a : ℝ) (ha : physical a) (h0 : rf0619.DefinedAt a) (h1 : rf0637.DefinedAt a) (h2 : rf0655.DefinedAt a) (h3 : rf0673.DefinedAt a) (h4 : rf0691.DefinedAt a) (h5 : rf0709.DefinedAt a) (h6 : rf0727.DefinedAt a) :
    ∀ r : Fin 2,(∑ i,vectorF a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputF (false,4,2,0)) (regularOrbit r) ∧ (∑ i,vectorG a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputG (false,4,2,0)) (regularOrbit r) := by
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
  all_goals norm_num [evalQPoly,den,rf0655,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem repeated_values (a : ℝ) (ha : physical a) (h0 : rf0619.DefinedAt a) (h1 : rf0637.DefinedAt a) (h2 : rf0655.DefinedAt a) (h3 : rf0673.DefinedAt a) (h4 : rf0691.DefinedAt a) (h5 : rf0709.DefinedAt a) (h6 : rf0727.DefinedAt a) :
    ∀ r : Fin 3,(∑ i,vectorF a i*contactSigma a (Fin.castAdd 2 r)^i.val)+repeatedLambda a r*(∑ i,vectorG a i*contactSigma a (Fin.castAdd 2 r)^i.val)=orbitData a (standardInputF (false,4,2,0)) (Fin.castAdd 2 r)+repeatedLambda a r*orbitData a (standardInputG (false,4,2,0)) (Fin.castAdd 2 r) := by
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
  all_goals norm_num [evalQPoly,den,rf0655,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0619.DefinedAt a) (h1 : rf0637.DefinedAt a) (h2 : rf0655.DefinedAt a) (h3 : rf0673.DefinedAt a) (h4 : rf0691.DefinedAt a) (h5 : rf0709.DefinedAt a) (h6 : rf0727.DefinedAt a) :
    standardKernelFCoefficients a (false,4,2,0)=vectorF a ∧ standardKernelGCoefficients a (false,4,2,0)=vectorG a :=
  standard_coefficients_unique a ha _ _ _ (regular_values a ha h0 h1 h2 h3 h4 h5 h6) (repeated_values a ha h0 h1 h2 h3 h4 h5 h6)

#print axioms coefficients

def rawColumn9 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0619,rf0637,rf0013,rf0655,rf0013,rf0013,rf0673,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0691,rf0709,rf0013,rf0727,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (false,0,2,1),standardRawFeature minus (false,1,0,2),standardRawFeature minus (false,1,3,0),standardRawFeature minus (false,2,1,1),standardRawFeature minus (false,3,2,0),standardRawFeature minus (false,4,0,1),standardRawFeature minus (false,5,1,0),standardRawFeature minus (false,7,0,0),standardRawFeature minus (false,0,1,2),standardRawFeature minus (false,0,4,0),standardRawFeature minus (false,1,2,1),standardRawFeature minus (false,2,0,2),standardRawFeature minus (false,2,3,0),standardRawFeature minus (false,3,1,1),standardRawFeature minus (false,4,2,0),standardRawFeature minus (false,5,0,1),standardRawFeature minus (false,6,1,0),standardRawFeature minus (false,8,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0),standardRawFeature minus (true,0,0,2),standardRawFeature minus (true,0,3,0),standardRawFeature minus (true,1,1,1),standardRawFeature minus (true,2,2,0),standardRawFeature minus (true,3,0,1),standardRawFeature minus (true,4,1,0),standardRawFeature minus (true,6,0,0),standardRawFeature minus (true,0,2,1),standardRawFeature minus (true,1,0,2),standardRawFeature minus (true,1,3,0),standardRawFeature minus (true,2,1,1),standardRawFeature minus (true,3,2,0),standardRawFeature minus (true,4,0,1),standardRawFeature minus (true,5,1,0),standardRawFeature minus (true,7,0,0)]

theorem raw_column_9 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0619.DefinedAt a) (h1 : rf0637.DefinedAt a) (h2 : rf0655.DefinedAt a) (h3 : rf0673.DefinedAt a) (h4 : rf0691.DefinedAt a) (h5 : rf0709.DefinedAt a) (h6 : rf0727.DefinedAt a) :
    rawColumn9 minus a=standardKernelFeature minus a (false,4,2,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Standard053
