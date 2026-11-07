import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd001
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0849.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (117/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-691/70 : ℚ)*Polynomial.X^5 + Polynomial.C (367/70 : ℚ)*Polynomial.X^6 + Polynomial.C (241/35 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf0849.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0849.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0849.rational a+Real.sqrt 2*evalQPoly rf0849.irrational a)/evalQPoly rf0849.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0849,rf0849]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (6/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/70 : ℚ)*Polynomial.X^2 + Polynomial.C (62/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-127/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-4/5 : ℚ)*Polynomial.X^5 + Polynomial.C (101/70 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf0853.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0853.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0853.rational a+Real.sqrt 2*evalQPoly rf0853.irrational a)/evalQPoly rf0853.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0853,rf0849]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (11/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/35 : ℚ)*Polynomial.X^2 + Polynomial.C (13/35 : ℚ)*Polynomial.X^3 + Polynomial.C (17/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf0861.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0861.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0861.rational a+Real.sqrt 2*evalQPoly rf0861.irrational a)/evalQPoly rf0861.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0861,rf0849]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/70 : ℚ)*Polynomial.X^2 + Polynomial.C (62/35 : ℚ)*Polynomial.X^3 + Polynomial.C (237/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-598/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1543/70 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf0857.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0857.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0857.rational a+Real.sqrt 2*evalQPoly rf0857.irrational a)/evalQPoly rf0857.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0857,rf0849]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^2 + Polynomial.C (64/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-108/35 : ℚ)*Polynomial.X^4 + Polynomial.C (62/35 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf0864.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0864.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0864.rational a+Real.sqrt 2*evalQPoly rf0864.irrational a)/evalQPoly rf0864.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0864,rf0849]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (2/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-2 : ℚ)*Polynomial.X^4
theorem eval5 (a : ℝ) (h : rf0872.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0872.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0872.rational a+Real.sqrt 2*evalQPoly rf0872.irrational a)/evalQPoly rf0872.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0872,rf0849]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^2 + Polynomial.C (51/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-67/14 : ℚ)*Polynomial.X^4 + Polynomial.C (369/70 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf0868.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0868.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0868.rational a+Real.sqrt 2*evalQPoly rf0868.irrational a)/evalQPoly rf0868.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0868,rf0849]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (32/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-54/35 : ℚ)*Polynomial.X^3 + Polynomial.C (31/35 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf0875.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0875.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0875.rational a+Real.sqrt 2*evalQPoly rf0875.irrational a)/evalQPoly rf0875.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0875,rf0849]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (24/35 : ℚ)*Polynomial.X^2 + Polynomial.C (26/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-3 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf0878.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0878.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0878.rational a+Real.sqrt 2*evalQPoly rf0878.irrational a)/evalQPoly rf0878.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0878,rf0849]
  all_goals ring

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0849.eval a
  | 0,1 => -rf0853.eval a
  | 0,2 => -rf0861.eval a
  | 1,0 => -rf0857.eval a
  | 1,1 => -rf0864.eval a
  | 1,2 => -rf0872.eval a
  | 2,0 => -rf0868.eval a
  | 2,1 => -rf0875.eval a
  | 3,0 => -rf0878.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a true i)^r.1.val*(parityFiberZ a true i j)^r.2.val)=paritySourceData a true (0,1,1) i j := by
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
  rw [parity_sum_odd]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD]
  field_simp [hD]
  fin_cases i <;> fin_cases j
  all_goals norm_num [evalQPoly,den,rf0849,n0,n1,n2,n3,n4,n5,n6,n7,n8,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    ∀ r,parityKernelCoefficients a true (0,1,1) (parityIndexTag true r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8)

#print axioms coefficients

def rawColumn4 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0)]

theorem raw_column_4 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn4 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn4,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_4

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn5 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn6 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn7 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0),parityOdd*parityMonomial (0,1,3),parityOdd*parityMonomial (0,3,2),parityOdd*parityMonomial (0,5,1),parityOdd*parityMonomial (0,7,0),parityOdd*parityMonomial (1,0,3),parityOdd*parityMonomial (1,2,2),parityOdd*parityMonomial (1,4,1),parityOdd*parityMonomial (1,6,0),parityOdd*parityMonomial (2,1,2),parityOdd*parityMonomial (2,3,1),parityOdd*parityMonomial (2,5,0),parityOdd*parityMonomial (3,0,2),parityOdd*parityMonomial (3,2,1),parityOdd*parityMonomial (3,4,0),parityOdd*parityMonomial (4,1,1),parityOdd*parityMonomial (4,3,0),parityOdd*parityMonomial (5,0,1),parityOdd*parityMonomial (5,2,0),parityOdd*parityMonomial (6,1,0),parityOdd*parityMonomial (7,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn8 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0849,rf0853,rf0857,rf0013,rf0861,rf0864,rf0868,rf0012,rf0013,rf0013,rf0872,rf0875,rf0878,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityOdd*parityMonomial (0,0,0),parityOdd*parityMonomial (0,1,0),parityOdd*parityMonomial (1,0,0),parityOdd*parityMonomial (0,0,1),parityOdd*parityMonomial (0,2,0),parityOdd*parityMonomial (1,1,0),parityOdd*parityMonomial (2,0,0),parityOdd*parityMonomial (0,1,1),parityOdd*parityMonomial (0,3,0),parityOdd*parityMonomial (1,0,1),parityOdd*parityMonomial (1,2,0),parityOdd*parityMonomial (2,1,0),parityOdd*parityMonomial (3,0,0),parityOdd*parityMonomial (0,0,2),parityOdd*parityMonomial (0,2,1),parityOdd*parityMonomial (0,4,0),parityOdd*parityMonomial (1,1,1),parityOdd*parityMonomial (1,3,0),parityOdd*parityMonomial (2,0,1),parityOdd*parityMonomial (2,2,0),parityOdd*parityMonomial (3,1,0),parityOdd*parityMonomial (4,0,0),parityOdd*parityMonomial (0,1,2),parityOdd*parityMonomial (0,3,1),parityOdd*parityMonomial (0,5,0),parityOdd*parityMonomial (1,0,2),parityOdd*parityMonomial (1,2,1),parityOdd*parityMonomial (1,4,0),parityOdd*parityMonomial (2,1,1),parityOdd*parityMonomial (2,3,0),parityOdd*parityMonomial (3,0,1),parityOdd*parityMonomial (3,2,0),parityOdd*parityMonomial (4,1,0),parityOdd*parityMonomial (5,0,0),parityOdd*parityMonomial (0,0,3),parityOdd*parityMonomial (0,2,2),parityOdd*parityMonomial (0,4,1),parityOdd*parityMonomial (0,6,0),parityOdd*parityMonomial (1,1,2),parityOdd*parityMonomial (1,3,1),parityOdd*parityMonomial (1,5,0),parityOdd*parityMonomial (2,0,2),parityOdd*parityMonomial (2,2,1),parityOdd*parityMonomial (2,4,0),parityOdd*parityMonomial (3,1,1),parityOdd*parityMonomial (3,3,0),parityOdd*parityMonomial (4,0,1),parityOdd*parityMonomial (4,2,0),parityOdd*parityMonomial (5,1,0),parityOdd*parityMonomial (6,0,0),parityOdd*parityMonomial (0,1,3),parityOdd*parityMonomial (0,3,2),parityOdd*parityMonomial (0,5,1),parityOdd*parityMonomial (0,7,0),parityOdd*parityMonomial (1,0,3),parityOdd*parityMonomial (1,2,2),parityOdd*parityMonomial (1,4,1),parityOdd*parityMonomial (1,6,0),parityOdd*parityMonomial (2,1,2),parityOdd*parityMonomial (2,3,1),parityOdd*parityMonomial (2,5,0),parityOdd*parityMonomial (3,0,2),parityOdd*parityMonomial (3,2,1),parityOdd*parityMonomial (3,4,0),parityOdd*parityMonomial (4,1,1),parityOdd*parityMonomial (4,3,0),parityOdd*parityMonomial (5,0,1),parityOdd*parityMonomial (5,2,0),parityOdd*parityMonomial (6,1,0),parityOdd*parityMonomial (7,0,0),parityOdd*parityMonomial (0,0,4),parityOdd*parityMonomial (0,2,3),parityOdd*parityMonomial (0,4,2),parityOdd*parityMonomial (0,6,1),parityOdd*parityMonomial (0,8,0),parityOdd*parityMonomial (1,1,3),parityOdd*parityMonomial (1,3,2),parityOdd*parityMonomial (1,5,1),parityOdd*parityMonomial (1,7,0),parityOdd*parityMonomial (2,0,3),parityOdd*parityMonomial (2,2,2),parityOdd*parityMonomial (2,4,1),parityOdd*parityMonomial (2,6,0),parityOdd*parityMonomial (3,1,2),parityOdd*parityMonomial (3,3,1),parityOdd*parityMonomial (3,5,0),parityOdd*parityMonomial (4,0,2),parityOdd*parityMonomial (4,2,1),parityOdd*parityMonomial (4,4,0),parityOdd*parityMonomial (5,1,1),parityOdd*parityMonomial (5,3,0),parityOdd*parityMonomial (6,0,1),parityOdd*parityMonomial (6,2,0),parityOdd*parityMonomial (7,1,0),parityOdd*parityMonomial (8,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0849.DefinedAt a) (h1 : rf0853.DefinedAt a) (h2 : rf0861.DefinedAt a) (h3 : rf0857.DefinedAt a) (h4 : rf0864.DefinedAt a) (h5 : rf0872.DefinedAt a) (h6 : rf0868.DefinedAt a) (h7 : rf0875.DefinedAt a) (h8 : rf0878.DefinedAt a) :
    rawColumn9 a=parityKernelFeature true a (0,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_odd,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Odd001
