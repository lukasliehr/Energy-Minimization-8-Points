import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even017
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0887.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^2 + Polynomial.C (3/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/17 : ℚ)*Polynomial.X^4 + Polynomial.C (22/17 : ℚ)*Polynomial.X^5 + Polynomial.C (3/34 : ℚ)*Polynomial.X^6 + Polynomial.C (-13/17 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf0887.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0887.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0887.rational a+Real.sqrt 2*evalQPoly rf0887.irrational a)/evalQPoly rf0887.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0887,rf0887]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (4/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-10/17 : ℚ)*Polynomial.X^3 + Polynomial.C (5/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/34 : ℚ)*Polynomial.X^5 + Polynomial.C (19/17 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf0898.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0898.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0898.rational a+Real.sqrt 2*evalQPoly rf0898.irrational a)/evalQPoly rf0898.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0898,rf0887]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (5/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-5/17 : ℚ)*Polynomial.X^4 + Polynomial.C (1/2 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf0918.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0918.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0918.rational a+Real.sqrt 2*evalQPoly rf0918.irrational a)/evalQPoly rf0918.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0918,rf0887]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^2 + Polynomial.C (10/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-1 : ℚ)*Polynomial.X^4
theorem eval3 (a : ℝ) (h : rf0948.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0948.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0948.rational a+Real.sqrt 2*evalQPoly rf0948.irrational a)/evalQPoly rf0948.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0948,rf0887]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^2 + Polynomial.C (30/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-53/17 : ℚ)*Polynomial.X^4 + Polynomial.C (61/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-61/34 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf0907.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0907.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0907.rational a+Real.sqrt 2*evalQPoly rf0907.irrational a)/evalQPoly rf0907.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0907,rf0887]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/34 : ℚ)*Polynomial.X^1 + Polynomial.C (6/17 : ℚ)*Polynomial.X^2 + Polynomial.C (4/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-45/34 : ℚ)*Polynomial.X^4 + Polynomial.C (63/34 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf0928.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0928.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0928.rational a+Real.sqrt 2*evalQPoly rf0928.irrational a)/evalQPoly rf0928.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0928,rf0887]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/17 : ℚ)*Polynomial.X^1 + Polynomial.C (19/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-22/17 : ℚ)*Polynomial.X^3 + Polynomial.C (1/2 : ℚ)*Polynomial.X^4
theorem eval6 (a : ℝ) (h : rf0957.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0957.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0957.rational a+Real.sqrt 2*evalQPoly rf0957.irrational a)/evalQPoly rf0957.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0957,rf0887]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (6/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-21/17 : ℚ)*Polynomial.X^2 + Polynomial.C (36/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-93/34 : ℚ)*Polynomial.X^4 + Polynomial.C (26/17 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf0937.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0937.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0937.rational a+Real.sqrt 2*evalQPoly rf0937.irrational a)/evalQPoly rf0937.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0937,rf0887]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (5/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-14/17 : ℚ)*Polynomial.X^2 + Polynomial.C (23/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/34 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf0967.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0967.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0967.rational a+Real.sqrt 2*evalQPoly rf0967.irrational a)/evalQPoly rf0967.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0967,rf0887]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/17 : ℚ)*Polynomial.X^1 + Polynomial.C (27/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-1 : ℚ)*Polynomial.X^3
theorem eval9 (a : ℝ) (h : rf0811.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0811.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0811.rational a+Real.sqrt 2*evalQPoly rf0811.irrational a)/evalQPoly rf0811.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0811,rf0887]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (4/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/17 : ℚ)*Polynomial.X^3 + Polynomial.C (35/34 : ℚ)*Polynomial.X^4
theorem eval10 (a : ℝ) (h : rf0976.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0976.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0976.rational a+Real.sqrt 2*evalQPoly rf0976.irrational a)/evalQPoly rf0976.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0976,rf0887]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (-1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (5/17 : ℚ)*Polynomial.X^1 + Polynomial.C (1/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-21/17 : ℚ)*Polynomial.X^3
theorem eval11 (a : ℝ) (h : rf0995.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0995.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0995.rational a+Real.sqrt 2*evalQPoly rf0995.irrational a)/evalQPoly rf0995.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0995,rf0887]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0887.eval a
  | 0,1 => -rf0898.eval a
  | 0,2 => -rf0918.eval a
  | 0,3 => -rf0948.eval a
  | 1,0 => -rf0907.eval a
  | 1,1 => -rf0928.eval a
  | 1,2 => -rf0957.eval a
  | 2,0 => -rf0937.eval a
  | 2,1 => -rf0967.eval a
  | 2,2 => -rf0811.eval a
  | 3,0 => -rf0976.eval a
  | 3,1 => -rf0995.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (2,3,0) i j := by
  intro i j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h0
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
  rw [parity_sum_even]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD,eval9 a h9 hD,eval10 a h10 hD,eval11 a h11 hD]
  field_simp [hD]
  fin_cases i <;> fin_cases j
  all_goals norm_num [evalQPoly,den,rf0887,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (2,3,0) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0887,rf0898,rf0907,rf0013,rf0918,rf0928,rf0937,rf0013,rf0948,rf0013,rf0957,rf0967,rf0976,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0811,rf0995,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (2,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0887,rf0898,rf0907,rf0013,rf0918,rf0928,rf0937,rf0013,rf0948,rf0013,rf0957,rf0967,rf0976,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0811,rf0995,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (2,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0887,rf0898,rf0907,rf0013,rf0918,rf0928,rf0937,rf0013,rf0948,rf0013,rf0957,rf0967,rf0976,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0811,rf0995,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (2,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0887,rf0898,rf0907,rf0013,rf0918,rf0928,rf0937,rf0013,rf0948,rf0013,rf0957,rf0967,rf0976,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0811,rf0995,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (2,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0887,rf0898,rf0907,rf0013,rf0918,rf0928,rf0937,rf0013,rf0948,rf0013,rf0957,rf0967,rf0976,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0811,rf0995,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0887.DefinedAt a) (h1 : rf0898.DefinedAt a) (h2 : rf0918.DefinedAt a) (h3 : rf0948.DefinedAt a) (h4 : rf0907.DefinedAt a) (h5 : rf0928.DefinedAt a) (h6 : rf0957.DefinedAt a) (h7 : rf0937.DefinedAt a) (h8 : rf0967.DefinedAt a) (h9 : rf0811.DefinedAt a) (h10 : rf0976.DefinedAt a) (h11 : rf0995.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (2,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even017
