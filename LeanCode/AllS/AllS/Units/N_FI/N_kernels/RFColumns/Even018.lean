import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even018
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf0888.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (53/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (801/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-13771/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (719/782 : ℚ)*Polynomial.X^7 + Polynomial.C (-47631/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (4763/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-12741/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-10609/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (25477/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-6299/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (-83411/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (-6261/27370 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf0888.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0888.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0888.rational a+Real.sqrt 2*evalQPoly rf0888.irrational a)/evalQPoly rf0888.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0888,rf0888]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (403/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-489/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (78/805 : ℚ)*Polynomial.X^6 + Polynomial.C (2491/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-3117/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (5013/6440 : ℚ)*Polynomial.X^9 + Polynomial.C (1749/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (-23739/15640 : ℚ)*Polynomial.X^11 + Polynomial.C (2839/3220 : ℚ)*Polynomial.X^12 + Polynomial.C (7481/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-23/85 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf0899.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0899.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0899.rational a+Real.sqrt 2*evalQPoly rf0899.irrational a)/evalQPoly rf0899.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0899,rf0888]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (1/1610 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-447/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (820/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-14578/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (3161/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-491/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-42247/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (3107/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (3118/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (52/161 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf0919.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0919.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0919.rational a+Real.sqrt 2*evalQPoly rf0919.irrational a)/evalQPoly rf0919.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0919,rf0888]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-2/805 : ℚ)*Polynomial.X^6 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-402/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-106/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1514/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-1882/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (6/115 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf0949.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0949.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0949.rational a+Real.sqrt 2*evalQPoly rf0949.irrational a)/evalQPoly rf0949.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0949,rf0888]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-797/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2603/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-45383/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (38659/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-11301/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2293/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (12017/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-12713/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (57679/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-122433/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-31293/54740 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf0908.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0908.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0908.rational a+Real.sqrt 2*evalQPoly rf0908.irrational a)/evalQPoly rf0908.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0908,rf0888]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (1/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-383/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (71/1564 : ℚ)*Polynomial.X^4 + Polynomial.C (-324/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (2281/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (14341/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-139957/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (57/70 : ℚ)*Polynomial.X^9 + Polynomial.C (153529/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-171459/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (9241/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-1281/1955 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf0929.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0929.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0929.rational a+Real.sqrt 2*evalQPoly rf0929.irrational a)/evalQPoly rf0929.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0929,rf0888]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (27/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (453/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3631/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (132/161 : ℚ)*Polynomial.X^6 + Polynomial.C (-12769/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-5938/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (38061/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (124/805 : ℚ)*Polynomial.X^10 + Polynomial.C (-30377/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (277/805 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf0958.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0958.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0958.rational a+Real.sqrt 2*evalQPoly rf0958.irrational a)/evalQPoly rf0958.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0958,rf0888]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (2/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (1/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-7627/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (1126/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-3462/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (2411/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (6607/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-28274/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-12468/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (18507/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-12577/54740 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf0938.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0938.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0938.rational a+Real.sqrt 2*evalQPoly rf0938.irrational a)/evalQPoly rf0938.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0938,rf0888]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (37/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-1691/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (176/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (3984/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-12097/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (4009/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (8305/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (-4121/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (1568/1955 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf0968.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0968.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0968.rational a+Real.sqrt 2*evalQPoly rf0968.irrational a)/evalQPoly rf0968.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0968,rf0888]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-463/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (3592/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-2111/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (11136/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (533/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-22311/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (1443/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-275/322 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf0987.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0987.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0987.rational a+Real.sqrt 2*evalQPoly rf0987.irrational a)/evalQPoly rf0987.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0987,rf0888]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (43/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (-241/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-91/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (9024/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-7197/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-36511/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (31203/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (8601/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (2889/3910 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf0977.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0977.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0977.rational a+Real.sqrt 2*evalQPoly rf0977.irrational a)/evalQPoly rf0977.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0977,rf0888]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (172/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1727/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1858/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-264/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-509/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (39509/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-33871/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (2088/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-693/1955 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf0996.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0996.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0996.rational a+Real.sqrt 2*evalQPoly rf0996.irrational a)/evalQPoly rf0996.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0996,rf0888]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0888.eval a
  | 0,1 => -rf0899.eval a
  | 0,2 => -rf0919.eval a
  | 0,3 => -rf0949.eval a
  | 1,0 => -rf0908.eval a
  | 1,1 => -rf0929.eval a
  | 1,2 => -rf0958.eval a
  | 2,0 => -rf0938.eval a
  | 2,1 => -rf0968.eval a
  | 2,2 => -rf0987.eval a
  | 3,0 => -rf0977.eval a
  | 3,1 => -rf0996.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (3,0,1) i j := by
  intro i j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hbase : evalQPoly rf0888.denominator a≠0 := h0
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
  all_goals norm_num [evalQPoly,den,rf0888,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (3,0,1) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0888,rf0899,rf0908,rf0013,rf0919,rf0929,rf0938,rf0013,rf0949,rf0013,rf0958,rf0968,rf0977,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0987,rf0996,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0888,rf0899,rf0908,rf0013,rf0919,rf0929,rf0938,rf0013,rf0949,rf0013,rf0958,rf0968,rf0977,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0987,rf0996,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0888,rf0899,rf0908,rf0013,rf0919,rf0929,rf0938,rf0013,rf0949,rf0013,rf0958,rf0968,rf0977,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0987,rf0996,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0888,rf0899,rf0908,rf0013,rf0919,rf0929,rf0938,rf0013,rf0949,rf0013,rf0958,rf0968,rf0977,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0987,rf0996,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0888,rf0899,rf0908,rf0013,rf0919,rf0929,rf0938,rf0013,rf0949,rf0013,rf0958,rf0968,rf0977,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0987,rf0996,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0888.DefinedAt a) (h1 : rf0899.DefinedAt a) (h2 : rf0919.DefinedAt a) (h3 : rf0949.DefinedAt a) (h4 : rf0908.DefinedAt a) (h5 : rf0929.DefinedAt a) (h6 : rf0958.DefinedAt a) (h7 : rf0938.DefinedAt a) (h8 : rf0968.DefinedAt a) (h9 : rf0987.DefinedAt a) (h10 : rf0977.DefinedAt a) (h11 : rf0996.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even018
