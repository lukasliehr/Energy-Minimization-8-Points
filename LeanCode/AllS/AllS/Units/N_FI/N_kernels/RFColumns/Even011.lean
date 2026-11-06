import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even011
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0881.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (43/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/644 : ℚ)*Polynomial.X^3 + Polynomial.C (1117/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (267/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (6534/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-15991/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (138953/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-326477/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-9157/805 : ℚ)*Polynomial.X^10 + Polynomial.C (647699/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (97753/27370 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf0881.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0881.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0881.rational a+Real.sqrt 2*evalQPoly rf0881.irrational a)/evalQPoly rf0881.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0881,rf0881]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (-1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (19/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-18/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (311/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-8/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-142/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-3398/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2454/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (251/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-49501/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-39188/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (619/85 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf0892.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0892.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0892.rational a+Real.sqrt 2*evalQPoly rf0892.irrational a)/evalQPoly rf0892.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0892,rf0881]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (254/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-16/119 : ℚ)*Polynomial.X^4 + Polynomial.C (9368/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-28211/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (35762/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (1924/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-42377/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (25/322 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf0912.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0912.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0912.rational a+Real.sqrt 2*evalQPoly rf0912.irrational a)/evalQPoly rf0912.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0912,rf0881]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (41/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (73/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^4 + Polynomial.C (1077/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-1291/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-10273/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (58516/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-528/115 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf0942.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0942.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0942.rational a+Real.sqrt 2*evalQPoly rf0942.irrational a)/evalQPoly rf0942.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0942,rf0881]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (33/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-43/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (65/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (193/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (-1699/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-82627/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (129809/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (-167427/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-101183/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (787169/54740 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf0901.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0901.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0901.rational a+Real.sqrt 2*evalQPoly rf0901.irrational a)/evalQPoly rf0901.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0901,rf0881]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-121/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (724/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2634/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1832/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-27656/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2036/805 : ℚ)*Polynomial.X^7 + Polynomial.C (12458/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-34728/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (31423/1955 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf0922.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0922.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0922.rational a+Real.sqrt 2*evalQPoly rf0922.irrational a)/evalQPoly rf0922.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0922,rf0881]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (6/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/115 : ℚ)*Polynomial.X^3 + Polynomial.C (-82/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (10454/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-7482/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (47238/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (86/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-1836/805 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf0951.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0951.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0951.rational a+Real.sqrt 2*evalQPoly rf0951.irrational a)/evalQPoly rf0951.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0951,rf0881]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (19/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-93/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (512/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-141/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-3529/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-13569/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (64716/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-426981/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (3181/782 : ℚ)*Polynomial.X^9 + Polynomial.C (-104749/54740 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf0931.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0931.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0931.rational a+Real.sqrt 2*evalQPoly rf0931.irrational a)/evalQPoly rf0931.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0931,rf0881]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (118/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-328/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (244/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-6218/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (10002/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (18136/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-7627/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (2891/1955 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf0961.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0961.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0961.rational a+Real.sqrt 2*evalQPoly rf0961.irrational a)/evalQPoly rf0961.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0961,rf0881]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (26/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-836/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (3287/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1164/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (15978/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-3844/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (533/322 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf0981.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0981.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0981.rational a+Real.sqrt 2*evalQPoly rf0981.irrational a)/evalQPoly rf0981.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0981,rf0881]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/595 : ℚ)*Polynomial.X^2 + Polynomial.C (12/595 : ℚ)*Polynomial.X^3 + Polynomial.C (33/595 : ℚ)*Polynomial.X^4 + Polynomial.C (-5163/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-8/391 : ℚ)*Polynomial.X^6 + Polynomial.C (848/391 : ℚ)*Polynomial.X^7 + Polynomial.C (-15877/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-17217/3910 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf0970.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0970.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0970.rational a+Real.sqrt 2*evalQPoly rf0970.irrational a)/evalQPoly rf0970.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0970,rf0881]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (142/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-608/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1746/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-5692/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (402/805 : ℚ)*Polynomial.X^6 + Polynomial.C (24296/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-7326/1955 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf0989.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0989.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0989.rational a+Real.sqrt 2*evalQPoly rf0989.irrational a)/evalQPoly rf0989.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0989,rf0881]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0881.eval a
  | 0,1 => -rf0892.eval a
  | 0,2 => -rf0912.eval a
  | 0,3 => -rf0942.eval a
  | 1,0 => -rf0901.eval a
  | 1,1 => -rf0922.eval a
  | 1,2 => -rf0951.eval a
  | 2,0 => -rf0931.eval a
  | 2,1 => -rf0961.eval a
  | 2,2 => -rf0981.eval a
  | 3,0 => -rf0970.eval a
  | 3,1 => -rf0989.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (0,3,1) i j := by
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
  all_goals norm_num [evalQPoly,den,rf0881,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (0,3,1) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0881,rf0892,rf0901,rf0013,rf0912,rf0922,rf0931,rf0013,rf0942,rf0013,rf0951,rf0961,rf0970,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0981,rf0989,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0881,rf0892,rf0901,rf0013,rf0912,rf0922,rf0931,rf0013,rf0942,rf0013,rf0951,rf0961,rf0970,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0981,rf0989,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0881,rf0892,rf0901,rf0013,rf0912,rf0922,rf0931,rf0013,rf0942,rf0013,rf0951,rf0961,rf0970,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0981,rf0989,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0881,rf0892,rf0901,rf0013,rf0912,rf0922,rf0931,rf0013,rf0942,rf0013,rf0951,rf0961,rf0970,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0981,rf0989,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0881,rf0892,rf0901,rf0013,rf0912,rf0922,rf0931,rf0013,rf0942,rf0013,rf0951,rf0961,rf0970,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0981,rf0989,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0881.DefinedAt a) (h1 : rf0892.DefinedAt a) (h2 : rf0912.DefinedAt a) (h3 : rf0942.DefinedAt a) (h4 : rf0901.DefinedAt a) (h5 : rf0922.DefinedAt a) (h6 : rf0951.DefinedAt a) (h7 : rf0931.DefinedAt a) (h8 : rf0961.DefinedAt a) (h9 : rf0981.DefinedAt a) (h10 : rf0970.DefinedAt a) (h11 : rf0989.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (0,3,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even011
