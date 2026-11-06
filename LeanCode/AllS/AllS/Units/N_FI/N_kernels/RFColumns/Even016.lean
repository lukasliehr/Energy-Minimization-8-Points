import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even016
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0886.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-7/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-887/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (461/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-19177/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (40277/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-41829/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (36707/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (13009/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-77081/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (67377/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (1851/3910 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf0886.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0886.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0886.rational a+Real.sqrt 2*evalQPoly rf0886.irrational a)/evalQPoly rf0886.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0886,rf0886]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-179/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (387/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-201/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-3571/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (4713/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (14117/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-18679/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-6129/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (41/85 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf0897.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0897.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0897.rational a+Real.sqrt 2*evalQPoly rf0897.irrational a)/evalQPoly rf0897.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0897,rf0886]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (4/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (4/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-300/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (9049/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-21968/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (520/391 : ℚ)*Polynomial.X^8 + Polynomial.C (9444/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-29959/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-4/23 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf0917.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0917.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0917.rational a+Real.sqrt 2*evalQPoly rf0917.irrational a)/evalQPoly rf0917.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0917,rf0886]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-24/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (1209/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-1864/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-2306/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (7848/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-79/230 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf0947.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0947.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0947.rational a+Real.sqrt 2*evalQPoly rf0947.irrational a)/evalQPoly rf0947.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0947,rf0886]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (19/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (411/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-7737/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (7473/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-14436/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (11836/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (1517/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-61/85 : ℚ)*Polynomial.X^9 + Polynomial.C (5709/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-2549/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (10443/7820 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf0906.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0906.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0906.rational a+Real.sqrt 2*evalQPoly rf0906.irrational a)/evalQPoly rf0906.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0906,rf0886]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (331/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-18/391 : ℚ)*Polynomial.X^4 + Polynomial.C (241/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (223/782 : ℚ)*Polynomial.X^6 + Polynomial.C (-18019/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (9463/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (14129/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-778/391 : ℚ)*Polynomial.X^10 + Polynomial.C (1792/1955 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf0927.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0927.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0927.rational a+Real.sqrt 2*evalQPoly rf0927.irrational a)/evalQPoly rf0927.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0927,rf0886]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (832/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1016/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (12689/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-34/35 : ℚ)*Polynomial.X^7 + Polynomial.C (2708/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (77/391 : ℚ)*Polynomial.X^9 + Polynomial.C (-9/230 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf0956.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0956.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0956.rational a+Real.sqrt 2*evalQPoly rf0956.irrational a)/evalQPoly rf0956.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0956,rf0886]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/2380 : ℚ)*Polynomial.X^3 + Polynomial.C (489/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-1213/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (67/170 : ℚ)*Polynomial.X^6 + Polynomial.C (-791/782 : ℚ)*Polynomial.X^7 + Polynomial.C (104519/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-68219/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1767/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-5653/7820 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf0936.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0936.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0936.rational a+Real.sqrt 2*evalQPoly rf0936.irrational a)/evalQPoly rf0936.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0936,rf0886]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (3/1610 : ℚ)*Polynomial.X^3 + Polynomial.C (-837/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (3693/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-1133/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-4863/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (5101/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-13296/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1243/3910 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf0966.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0966.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0966.rational a+Real.sqrt 2*evalQPoly rf0966.irrational a)/evalQPoly rf0966.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0966,rf0886]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (6/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (464/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3273/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (8793/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-7138/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-1588/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (22217/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (7/46 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf0986.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0986.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0986.rational a+Real.sqrt 2*evalQPoly rf0986.irrational a)/evalQPoly rf0986.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0986,rf0886]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (6/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (2/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (2146/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-2587/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-1345/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (3291/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^8 + Polynomial.C (-10751/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-899/1955 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf0975.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0975.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0975.rational a+Real.sqrt 2*evalQPoly rf0975.irrational a)/evalQPoly rf0975.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0975,rf0886]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (3/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (1293/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2561/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-11583/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (649/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (96/115 : ℚ)*Polynomial.X^8 + Polynomial.C (-1274/1955 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf0994.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0994.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0994.rational a+Real.sqrt 2*evalQPoly rf0994.irrational a)/evalQPoly rf0994.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0994,rf0886]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0886.eval a
  | 0,1 => -rf0897.eval a
  | 0,2 => -rf0917.eval a
  | 0,3 => -rf0947.eval a
  | 1,0 => -rf0906.eval a
  | 1,1 => -rf0927.eval a
  | 1,2 => -rf0956.eval a
  | 2,0 => -rf0936.eval a
  | 2,1 => -rf0966.eval a
  | 2,2 => -rf0986.eval a
  | 3,0 => -rf0975.eval a
  | 3,1 => -rf0994.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (2,1,1) i j := by
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
  all_goals norm_num [evalQPoly,den,rf0886,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (2,1,1) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0886,rf0897,rf0906,rf0013,rf0917,rf0927,rf0936,rf0013,rf0947,rf0013,rf0956,rf0966,rf0975,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0986,rf0994,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (2,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0886,rf0897,rf0906,rf0013,rf0917,rf0927,rf0936,rf0013,rf0947,rf0013,rf0956,rf0966,rf0975,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0986,rf0994,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (2,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0886,rf0897,rf0906,rf0013,rf0917,rf0927,rf0936,rf0013,rf0947,rf0013,rf0956,rf0966,rf0975,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0986,rf0994,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (2,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0886,rf0897,rf0906,rf0013,rf0917,rf0927,rf0936,rf0013,rf0947,rf0013,rf0956,rf0966,rf0975,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0986,rf0994,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (2,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0886,rf0897,rf0906,rf0013,rf0917,rf0927,rf0936,rf0013,rf0947,rf0013,rf0956,rf0966,rf0975,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0986,rf0994,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0886.DefinedAt a) (h1 : rf0897.DefinedAt a) (h2 : rf0917.DefinedAt a) (h3 : rf0947.DefinedAt a) (h4 : rf0906.DefinedAt a) (h5 : rf0927.DefinedAt a) (h6 : rf0956.DefinedAt a) (h7 : rf0936.DefinedAt a) (h8 : rf0966.DefinedAt a) (h9 : rf0986.DefinedAt a) (h10 : rf0975.DefinedAt a) (h11 : rf0994.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (2,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even016
