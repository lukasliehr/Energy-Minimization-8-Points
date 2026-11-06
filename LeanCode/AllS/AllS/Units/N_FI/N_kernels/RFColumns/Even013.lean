import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even013
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf0883.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (57/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-409/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-65/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (57541/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-206681/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (394929/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-91991/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (5375701/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-353407/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (1550471/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-76849/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (-11317/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (73925/10948 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf0883.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0883.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0883.rational a+Real.sqrt 2*evalQPoly rf0883.irrational a)/evalQPoly rf0883.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0883,rf0883]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (9/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-31/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (27/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (641/31280 : ℚ)*Polynomial.X^5 + Polynomial.C (-111/680 : ℚ)*Polynomial.X^6 + Polynomial.C (1613/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-5101/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-19927/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (465571/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-48251/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (1189/476 : ℚ)*Polynomial.X^12 + Polynomial.C (59881/43792 : ℚ)*Polynomial.X^13 + Polynomial.C (-137/136 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf0894.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0894.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0894.rational a+Real.sqrt 2*evalQPoly rf0894.irrational a)/evalQPoly rf0894.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0894,rf0883]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (229/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (367/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-7433/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (108089/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-39845/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (50571/1610 : ℚ)*Polynomial.X^9 + Polynomial.C (-30709/782 : ℚ)*Polynomial.X^10 + Polynomial.C (1266197/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (10809/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-4705/644 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf0914.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0914.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0914.rational a+Real.sqrt 2*evalQPoly rf0914.irrational a)/evalQPoly rf0914.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0914,rf0883]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-33/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (81/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-5293/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (66/391 : ℚ)*Polynomial.X^9 + Polynomial.C (19699/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-17601/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (25/92 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf0944.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0944.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0944.rational a+Real.sqrt 2*evalQPoly rf0944.irrational a)/evalQPoly rf0944.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0944,rf0883]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/805 : ℚ)*Polynomial.X^2 + Polynomial.C (87/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1991/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-70169/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (209393/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-177391/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (734971/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-3454747/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (295959/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (44824/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (-1709389/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (851117/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (71665/10948 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf0903.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0903.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0903.rational a+Real.sqrt 2*evalQPoly rf0903.irrational a)/evalQPoly rf0903.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0903,rf0883]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (1/391 : ℚ)*Polynomial.X^3 + Polynomial.C (-2827/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (865/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-4041/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (7046/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-27011/31280 : ℚ)*Polynomial.X^8 + Polynomial.C (-35187/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (14521/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-2385/391 : ℚ)*Polynomial.X^11 + Polynomial.C (959359/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-3775/3128 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf0924.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0924.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0924.rational a+Real.sqrt 2*evalQPoly rf0924.irrational a)/evalQPoly rf0924.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0924,rf0883]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-72/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1031/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (373/805 : ℚ)*Polynomial.X^5 + Polynomial.C (-81563/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (140174/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-563627/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (636911/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-629367/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-2798/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (1641/644 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf0953.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0953.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0953.rational a+Real.sqrt 2*evalQPoly rf0953.irrational a)/evalQPoly rf0953.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0953,rf0883]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-39/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-39/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (8091/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-4766/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (90682/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-246034/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (188441/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-3683/85 : ℚ)*Polynomial.X^10 + Polynomial.C (23829/805 : ℚ)*Polynomial.X^11 + Polynomial.C (-26893/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-45467/5474 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf0933.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0933.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0933.rational a+Real.sqrt 2*evalQPoly rf0933.irrational a)/evalQPoly rf0933.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0933,rf0883]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (27/21896 : ℚ)*Polynomial.X^3 + Polynomial.C (-118/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1/460 : ℚ)*Polynomial.X^5 + Polynomial.C (593/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-28837/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (5931/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (16373/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (-144199/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (33797/15640 : ℚ)*Polynomial.X^11 + Polynomial.C (-245/391 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf0963.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0963.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0963.rational a+Real.sqrt 2*evalQPoly rf0963.irrational a)/evalQPoly rf0963.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0963,rf0883]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (181/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (96/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-1962/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (51293/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-147227/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (241908/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-195971/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (30789/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (1413/322 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf0983.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0983.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0983.rational a+Real.sqrt 2*evalQPoly rf0983.irrational a)/evalQPoly rf0983.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0983,rf0883]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (11/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-151/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-579/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (17727/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-62479/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (87041/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (75179/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-892681/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1135233/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-267483/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-9627/1564 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf0972.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0972.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0972.rational a+Real.sqrt 2*evalQPoly rf0972.irrational a)/evalQPoly rf0972.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0972,rf0883]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3128 : ℚ)*Polynomial.X^2 + Polynomial.C (-269/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (1007/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-31/805 : ℚ)*Polynomial.X^5 + Polynomial.C (5567/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-5643/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-13597/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (15488/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-157281/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (873/1564 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf0991.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0991.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0991.rational a+Real.sqrt 2*evalQPoly rf0991.irrational a)/evalQPoly rf0991.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0991,rf0883]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0883.eval a
  | 0,1 => -rf0894.eval a
  | 0,2 => -rf0914.eval a
  | 0,3 => -rf0944.eval a
  | 1,0 => -rf0903.eval a
  | 1,1 => -rf0924.eval a
  | 1,2 => -rf0953.eval a
  | 2,0 => -rf0933.eval a
  | 2,1 => -rf0963.eval a
  | 2,2 => -rf0983.eval a
  | 3,0 => -rf0972.eval a
  | 3,1 => -rf0991.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (1,0,2) i j := by
  intro i j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hbase : evalQPoly rf0883.denominator a≠0 := h0
  have hD : evalQPoly den a≠0 := by
    simpa [den,evalQPoly] using mul_ne_zero ha0 hbase
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
  all_goals norm_num [evalQPoly,den,rf0883,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (1,0,2) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0883,rf0894,rf0903,rf0013,rf0914,rf0924,rf0933,rf0013,rf0944,rf0013,rf0953,rf0963,rf0972,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0983,rf0991,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0883,rf0894,rf0903,rf0013,rf0914,rf0924,rf0933,rf0013,rf0944,rf0013,rf0953,rf0963,rf0972,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0983,rf0991,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0883,rf0894,rf0903,rf0013,rf0914,rf0924,rf0933,rf0013,rf0944,rf0013,rf0953,rf0963,rf0972,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0983,rf0991,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0883,rf0894,rf0903,rf0013,rf0914,rf0924,rf0933,rf0013,rf0944,rf0013,rf0953,rf0963,rf0972,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0983,rf0991,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0883,rf0894,rf0903,rf0013,rf0914,rf0924,rf0933,rf0013,rf0944,rf0013,rf0953,rf0963,rf0972,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0983,rf0991,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0883.DefinedAt a) (h1 : rf0894.DefinedAt a) (h2 : rf0914.DefinedAt a) (h3 : rf0944.DefinedAt a) (h4 : rf0903.DefinedAt a) (h5 : rf0924.DefinedAt a) (h6 : rf0953.DefinedAt a) (h7 : rf0933.DefinedAt a) (h8 : rf0963.DefinedAt a) (h9 : rf0983.DefinedAt a) (h10 : rf0972.DefinedAt a) (h11 : rf0991.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (1,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even013
