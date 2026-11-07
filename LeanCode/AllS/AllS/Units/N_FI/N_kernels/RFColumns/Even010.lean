import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even010
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0880.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-57/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (639/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (226/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3777/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (34143/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-11149/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (173804/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-51070/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (679267/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-1425189/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (240574/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-73499/10948 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf0880.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0880.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0880.rational a+Real.sqrt 2*evalQPoly rf0880.irrational a)/evalQPoly rf0880.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0880,rf0880]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-39/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (319/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-1703/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (8129/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-16547/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (42779/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-39919/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-47879/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (131273/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-686261/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (160773/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (101/136 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf0891.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0891.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0891.rational a+Real.sqrt 2*evalQPoly rf0891.irrational a)/evalQPoly rf0891.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0891,rf0880]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (31/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-503/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (486/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-15/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-11567/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (177/34 : ℚ)*Polynomial.X^7 + Polynomial.C (-43242/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (1442649/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-641129/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (5849/644 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf0911.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0911.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0911.rational a+Real.sqrt 2*evalQPoly rf0911.irrational a)/evalQPoly rf0911.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0911,rf0880]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-67/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-32/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (947/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-264/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (8213/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-2336/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-53749/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (5860/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-109/92 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf0941.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0941.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0941.rational a+Real.sqrt 2*evalQPoly rf0941.irrational a)/evalQPoly rf0941.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0941,rf0880]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (41/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-127/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-89/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (8917/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-57843/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (100757/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-23847/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (403833/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (50557/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-100199/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (969181/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-38449/5474 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf0900.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0900.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0900.rational a+Real.sqrt 2*evalQPoly rf0900.irrational a)/evalQPoly rf0900.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0900,rf0880]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (19/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (-407/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (7323/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-3923/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (71003/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-83473/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-221717/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (1081491/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-205791/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (18529/3128 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf0921.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0921.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0921.rational a+Real.sqrt 2*evalQPoly rf0921.irrational a)/evalQPoly rf0921.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0921,rf0880]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (83/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (228/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-5939/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (15906/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-107013/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (124548/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-765067/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (9803/805 : ℚ)*Polynomial.X^9 + Polynomial.C (-2805/644 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf0950.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0950.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0950.rational a+Real.sqrt 2*evalQPoly rf0950.irrational a)/evalQPoly rf0950.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0950,rf0880]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^1 + Polynomial.C (261/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-237/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-3691/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2830/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-13637/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (104611/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-774283/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (42579/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-1177567/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (54867/5474 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf0930.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0930.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0930.rational a+Real.sqrt 2*evalQPoly rf0930.irrational a)/evalQPoly rf0930.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0930,rf0880]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (-43/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (2/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-2173/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (7477/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-5452/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-6492/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (17061/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-16481/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (231/391 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf0960.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0960.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0960.rational a+Real.sqrt 2*evalQPoly rf0960.irrational a)/evalQPoly rf0960.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0960,rf0880]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (1/1190 : ℚ)*Polynomial.X^1 + Polynomial.C (-18/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (106/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (2753/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-4023/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (66798/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-124902/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (266839/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-1557/322 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf0980.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0980.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0980.rational a+Real.sqrt 2*evalQPoly rf0980.irrational a)/evalQPoly rf0980.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0980,rf0880]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (243/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (76/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-10113/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2931/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-62453/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-19496/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (523391/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-350167/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (10909/1564 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf0969.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0969.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0969.rational a+Real.sqrt 2*evalQPoly rf0969.irrational a)/evalQPoly rf0969.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0969,rf0880]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (-58/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (412/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3023/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1391/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-3012/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-614/805 : ℚ)*Polynomial.X^7 + Polynomial.C (6981/3220 : ℚ)*Polynomial.X^8 + Polynomial.C (-2119/1564 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf0988.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0988.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0988.rational a+Real.sqrt 2*evalQPoly rf0988.irrational a)/evalQPoly rf0988.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0988,rf0880]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0880.eval a
  | 0,1 => -rf0891.eval a
  | 0,2 => -rf0911.eval a
  | 0,3 => -rf0941.eval a
  | 1,0 => -rf0900.eval a
  | 1,1 => -rf0921.eval a
  | 1,2 => -rf0950.eval a
  | 2,0 => -rf0930.eval a
  | 2,1 => -rf0960.eval a
  | 2,2 => -rf0980.eval a
  | 3,0 => -rf0969.eval a
  | 3,1 => -rf0988.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (0,1,2) i j := by
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
  all_goals norm_num [evalQPoly,den,rf0880,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (0,1,2) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0880,rf0891,rf0900,rf0013,rf0911,rf0921,rf0930,rf0013,rf0941,rf0013,rf0950,rf0960,rf0969,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0980,rf0988,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (0,1,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0880,rf0891,rf0900,rf0013,rf0911,rf0921,rf0930,rf0013,rf0941,rf0013,rf0950,rf0960,rf0969,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0980,rf0988,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (0,1,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0880,rf0891,rf0900,rf0013,rf0911,rf0921,rf0930,rf0013,rf0941,rf0013,rf0950,rf0960,rf0969,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0980,rf0988,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (0,1,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0880,rf0891,rf0900,rf0013,rf0911,rf0921,rf0930,rf0013,rf0941,rf0013,rf0950,rf0960,rf0969,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0980,rf0988,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (0,1,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0880,rf0891,rf0900,rf0013,rf0911,rf0921,rf0930,rf0013,rf0941,rf0013,rf0950,rf0960,rf0969,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0980,rf0988,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0880.DefinedAt a) (h1 : rf0891.DefinedAt a) (h2 : rf0911.DefinedAt a) (h3 : rf0941.DefinedAt a) (h4 : rf0900.DefinedAt a) (h5 : rf0921.DefinedAt a) (h6 : rf0950.DefinedAt a) (h7 : rf0930.DefinedAt a) (h8 : rf0960.DefinedAt a) (h9 : rf0980.DefinedAt a) (h10 : rf0969.DefinedAt a) (h11 : rf0988.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (0,1,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even010
