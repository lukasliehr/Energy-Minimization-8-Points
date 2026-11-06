import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Standard033
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0465.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/80 : ℚ)*Polynomial.X^2 + Polynomial.C (57/40 : ℚ)*Polynomial.X^3 + Polynomial.C (-149/16 : ℚ)*Polynomial.X^4 + Polynomial.C (629/20 : ℚ)*Polynomial.X^5 + Polynomial.C (-4581/80 : ℚ)*Polynomial.X^6 + Polynomial.C (1909/40 : ℚ)*Polynomial.X^7 + Polynomial.C (49/80 : ℚ)*Polynomial.X^8 + Polynomial.C (-209/10 : ℚ)*Polynomial.X^9 + Polynomial.C (-39/20 : ℚ)*Polynomial.X^10 + Polynomial.C (-9/2 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf0435.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0435.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0435.rational a+Real.sqrt 2*evalQPoly rf0435.irrational a)/evalQPoly rf0435.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0435,rf0465]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/120 : ℚ)*Polynomial.X^1 + Polynomial.C (117/80 : ℚ)*Polynomial.X^2 + Polynomial.C (-183/20 : ℚ)*Polynomial.X^3 + Polynomial.C (6757/240 : ℚ)*Polynomial.X^4 + Polynomial.C (-4907/120 : ℚ)*Polynomial.X^5 + Polynomial.C (2413/240 : ℚ)*Polynomial.X^6 + Polynomial.C (1181/30 : ℚ)*Polynomial.X^7 + Polynomial.C (-6133/240 : ℚ)*Polynomial.X^8 + Polynomial.C (-184/15 : ℚ)*Polynomial.X^9 + Polynomial.C (-83/12 : ℚ)*Polynomial.X^10 + Polynomial.C (-11/2 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf0450.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0450.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0450.rational a+Real.sqrt 2*evalQPoly rf0450.irrational a)/evalQPoly rf0450.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0450,rf0465]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (-1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (1/30 : ℚ)*Polynomial.X^1 + Polynomial.C (23/80 : ℚ)*Polynomial.X^2 + Polynomial.C (-523/120 : ℚ)*Polynomial.X^3 + Polynomial.C (1599/80 : ℚ)*Polynomial.X^4 + Polynomial.C (-847/20 : ℚ)*Polynomial.X^5 + Polynomial.C (9203/240 : ℚ)*Polynomial.X^6 + Polynomial.C (47/40 : ℚ)*Polynomial.X^7 + Polynomial.C (-791/60 : ℚ)*Polynomial.X^8 + Polynomial.C (29/30 : ℚ)*Polynomial.X^9 + Polynomial.C (-31/6 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf0465.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0465.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0465.rational a+Real.sqrt 2*evalQPoly rf0465.irrational a)/evalQPoly rf0465.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0465,rf0465]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/240 : ℚ)*Polynomial.X^0 + Polynomial.C (3/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/80 : ℚ)*Polynomial.X^2 + Polynomial.C (61/60 : ℚ)*Polynomial.X^3 + Polynomial.C (77/240 : ℚ)*Polynomial.X^4 + Polynomial.C (-493/120 : ℚ)*Polynomial.X^5 + Polynomial.C (251/48 : ℚ)*Polynomial.X^6 + Polynomial.C (-16/15 : ℚ)*Polynomial.X^7 + Polynomial.C (191/60 : ℚ)*Polynomial.X^8 + Polynomial.C (1/12 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf0480.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0480.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0480.rational a+Real.sqrt 2*evalQPoly rf0480.irrational a)/evalQPoly rf0480.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0480,rf0465]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (3/20 : ℚ)*Polynomial.X^2 + Polynomial.C (9/8 : ℚ)*Polynomial.X^3 + Polynomial.C (-61/5 : ℚ)*Polynomial.X^4 + Polynomial.C (1577/40 : ℚ)*Polynomial.X^5 + Polynomial.C (-203/4 : ℚ)*Polynomial.X^6 + Polynomial.C (139/40 : ℚ)*Polynomial.X^7 + Polynomial.C (407/10 : ℚ)*Polynomial.X^8 + Polynomial.C (-44/5 : ℚ)*Polynomial.X^9 + Polynomial.C (25/2 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf0495.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0495.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0495.rational a+Real.sqrt 2*evalQPoly rf0495.irrational a)/evalQPoly rf0495.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0495,rf0465]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (-1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (1/8 : ℚ)*Polynomial.X^1 + Polynomial.C (51/40 : ℚ)*Polynomial.X^2 + Polynomial.C (-443/40 : ℚ)*Polynomial.X^3 + Polynomial.C (1089/40 : ℚ)*Polynomial.X^4 + Polynomial.C (-453/40 : ℚ)*Polynomial.X^5 + Polynomial.C (-1891/40 : ℚ)*Polynomial.X^6 + Polynomial.C (1767/40 : ℚ)*Polynomial.X^7 + Polynomial.C (319/10 : ℚ)*Polynomial.X^8 + Polynomial.C (37/10 : ℚ)*Polynomial.X^9 + Polynomial.C (25/2 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf0510.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0510.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0510.rational a+Real.sqrt 2*evalQPoly rf0510.irrational a)/evalQPoly rf0510.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0510,rf0465]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (-1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (3/20 : ℚ)*Polynomial.X^1 + Polynomial.C (9/8 : ℚ)*Polynomial.X^2 + Polynomial.C (-61/5 : ℚ)*Polynomial.X^3 + Polynomial.C (1577/40 : ℚ)*Polynomial.X^4 + Polynomial.C (-203/4 : ℚ)*Polynomial.X^5 + Polynomial.C (139/40 : ℚ)*Polynomial.X^6 + Polynomial.C (407/10 : ℚ)*Polynomial.X^7 + Polynomial.C (-44/5 : ℚ)*Polynomial.X^8 + Polynomial.C (25/2 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf0525.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0525.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0525.rational a+Real.sqrt 2*evalQPoly rf0525.irrational a)/evalQPoly rf0525.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0525,rf0465]
  all_goals ring

def vectorF (a : ℝ) : Fin 4 → ℝ := ![-rf0435.eval a,-rf0450.eval a,-rf0465.eval a,-rf0480.eval a]
def vectorG (a : ℝ) : Fin 3 → ℝ := ![-rf0495.eval a,-rf0510.eval a,-rf0525.eval a]
theorem regular_values (a : ℝ) (ha : physical a) (h0 : rf0435.DefinedAt a) (h1 : rf0450.DefinedAt a) (h2 : rf0465.DefinedAt a) (h3 : rf0480.DefinedAt a) (h4 : rf0495.DefinedAt a) (h5 : rf0510.DefinedAt a) (h6 : rf0525.DefinedAt a) :
    ∀ r : Fin 2,(∑ i,vectorF a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputF (false,1,0,2)) (regularOrbit r) ∧ (∑ i,vectorG a i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputG (false,1,0,2)) (regularOrbit r) := by
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
  all_goals norm_num [evalQPoly,den,rf0465,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem repeated_values (a : ℝ) (ha : physical a) (h0 : rf0435.DefinedAt a) (h1 : rf0450.DefinedAt a) (h2 : rf0465.DefinedAt a) (h3 : rf0480.DefinedAt a) (h4 : rf0495.DefinedAt a) (h5 : rf0510.DefinedAt a) (h6 : rf0525.DefinedAt a) :
    ∀ r : Fin 3,(∑ i,vectorF a i*contactSigma a (Fin.castAdd 2 r)^i.val)+repeatedLambda a r*(∑ i,vectorG a i*contactSigma a (Fin.castAdd 2 r)^i.val)=orbitData a (standardInputF (false,1,0,2)) (Fin.castAdd 2 r)+repeatedLambda a r*orbitData a (standardInputG (false,1,0,2)) (Fin.castAdd 2 r) := by
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
  all_goals norm_num [evalQPoly,den,rf0465,n0,n1,n2,n3,n4,n5,n6,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,standardInputF,standardInputG,regularOrbit,repeatedLambda]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0435.DefinedAt a) (h1 : rf0450.DefinedAt a) (h2 : rf0465.DefinedAt a) (h3 : rf0480.DefinedAt a) (h4 : rf0495.DefinedAt a) (h5 : rf0510.DefinedAt a) (h6 : rf0525.DefinedAt a) :
    standardKernelFCoefficients a (false,1,0,2)=vectorF a ∧ standardKernelGCoefficients a (false,1,0,2)=vectorG a :=
  standard_coefficients_unique a ha _ _ _ (regular_values a ha h0 h1 h2 h3 h4 h5 h6) (repeated_values a ha h0 h1 h2 h3 h4 h5 h6)

#print axioms coefficients

def rawColumn8 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0435,rf0450,rf0013,rf0465,rf0013,rf0013,rf0480,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0495,rf0510,rf0013,rf0525,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (false,0,2,1),standardRawFeature minus (false,1,0,2),standardRawFeature minus (false,1,3,0),standardRawFeature minus (false,2,1,1),standardRawFeature minus (false,3,2,0),standardRawFeature minus (false,4,0,1),standardRawFeature minus (false,5,1,0),standardRawFeature minus (false,7,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0),standardRawFeature minus (true,0,0,2),standardRawFeature minus (true,0,3,0),standardRawFeature minus (true,1,1,1),standardRawFeature minus (true,2,2,0),standardRawFeature minus (true,3,0,1),standardRawFeature minus (true,4,1,0),standardRawFeature minus (true,6,0,0)]

theorem raw_column_8 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0435.DefinedAt a) (h1 : rf0450.DefinedAt a) (h2 : rf0465.DefinedAt a) (h3 : rf0480.DefinedAt a) (h4 : rf0495.DefinedAt a) (h5 : rf0510.DefinedAt a) (h6 : rf0525.DefinedAt a) :
    rawColumn8 minus a=standardKernelFeature minus a (false,1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (minus : Bool) (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0435,rf0450,rf0013,rf0465,rf0013,rf0013,rf0480,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0495,rf0510,rf0013,rf0525,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [standardRawFeature minus (false,0,0,0),standardRawFeature minus (false,1,0,0),standardRawFeature minus (false,0,1,0),standardRawFeature minus (false,2,0,0),standardRawFeature minus (false,0,0,1),standardRawFeature minus (false,1,1,0),standardRawFeature minus (false,3,0,0),standardRawFeature minus (false,0,2,0),standardRawFeature minus (false,1,0,1),standardRawFeature minus (false,2,1,0),standardRawFeature minus (false,4,0,0),standardRawFeature minus (false,0,1,1),standardRawFeature minus (false,1,2,0),standardRawFeature minus (false,2,0,1),standardRawFeature minus (false,3,1,0),standardRawFeature minus (false,5,0,0),standardRawFeature minus (false,0,0,2),standardRawFeature minus (false,0,3,0),standardRawFeature minus (false,1,1,1),standardRawFeature minus (false,2,2,0),standardRawFeature minus (false,3,0,1),standardRawFeature minus (false,4,1,0),standardRawFeature minus (false,6,0,0),standardRawFeature minus (false,0,2,1),standardRawFeature minus (false,1,0,2),standardRawFeature minus (false,1,3,0),standardRawFeature minus (false,2,1,1),standardRawFeature minus (false,3,2,0),standardRawFeature minus (false,4,0,1),standardRawFeature minus (false,5,1,0),standardRawFeature minus (false,7,0,0),standardRawFeature minus (false,0,1,2),standardRawFeature minus (false,0,4,0),standardRawFeature minus (false,1,2,1),standardRawFeature minus (false,2,0,2),standardRawFeature minus (false,2,3,0),standardRawFeature minus (false,3,1,1),standardRawFeature minus (false,4,2,0),standardRawFeature minus (false,5,0,1),standardRawFeature minus (false,6,1,0),standardRawFeature minus (false,8,0,0),standardRawFeature minus (true,0,0,0),standardRawFeature minus (true,1,0,0),standardRawFeature minus (true,0,1,0),standardRawFeature minus (true,2,0,0),standardRawFeature minus (true,0,0,1),standardRawFeature minus (true,1,1,0),standardRawFeature minus (true,3,0,0),standardRawFeature minus (true,0,2,0),standardRawFeature minus (true,1,0,1),standardRawFeature minus (true,2,1,0),standardRawFeature minus (true,4,0,0),standardRawFeature minus (true,0,1,1),standardRawFeature minus (true,1,2,0),standardRawFeature minus (true,2,0,1),standardRawFeature minus (true,3,1,0),standardRawFeature minus (true,5,0,0),standardRawFeature minus (true,0,0,2),standardRawFeature minus (true,0,3,0),standardRawFeature minus (true,1,1,1),standardRawFeature minus (true,2,2,0),standardRawFeature minus (true,3,0,1),standardRawFeature minus (true,4,1,0),standardRawFeature minus (true,6,0,0),standardRawFeature minus (true,0,2,1),standardRawFeature minus (true,1,0,2),standardRawFeature minus (true,1,3,0),standardRawFeature minus (true,2,1,1),standardRawFeature minus (true,3,2,0),standardRawFeature minus (true,4,0,1),standardRawFeature minus (true,5,1,0),standardRawFeature minus (true,7,0,0)]

theorem raw_column_9 (minus : Bool) (a : ℝ) (ha : physical a) (h0 : rf0435.DefinedAt a) (h1 : rf0450.DefinedAt a) (h2 : rf0465.DefinedAt a) (h3 : rf0480.DefinedAt a) (h4 : rf0495.DefinedAt a) (h5 : rf0510.DefinedAt a) (h6 : rf0525.DefinedAt a) :
    rawColumn9 minus a=standardKernelFeature minus a (false,1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [standardKernelFeature_expansion minus a ha,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).1,(coefficients a ha h0 h1 h2 h3 h4 h5 h6).2]
  cases minus
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vectorF,vectorG,invariantMonomial,standardRawFeature,standardPivotP,standardPivotQ]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Standard033
