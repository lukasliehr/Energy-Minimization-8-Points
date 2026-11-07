import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even008
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf0747.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/1190 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-617/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (10967/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-20563/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (79503/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-8252/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (128057/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-2463/1190 : ℚ)*Polynomial.X^11 + Polynomial.C (-26037/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (27073/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (9347/13685 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf0747.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0747.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0747.rational a+Real.sqrt 2*evalQPoly rf0747.irrational a)/evalQPoly rf0747.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0747,rf0747]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (29/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-39/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (1993/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-1947/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-583/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (3597/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-40757/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (1573/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-831/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (2469/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-11/170 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf0757.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0757.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0757.rational a+Real.sqrt 2*evalQPoly rf0757.irrational a)/evalQPoly rf0757.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0757,rf0747]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (36/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (63/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-5142/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (22038/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-44131/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (30687/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (38027/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-43721/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-109/161 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf0776.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0776.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0776.rational a+Real.sqrt 2*evalQPoly rf0776.irrational a)/evalQPoly rf0776.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0776,rf0747]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-2/805 : ℚ)*Polynomial.X^5 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-402/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-106/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (1514/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-1882/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (6/115 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf0803.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0803.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0803.rational a+Real.sqrt 2*evalQPoly rf0803.irrational a)/evalQPoly rf0803.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0803,rf0747]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^2 + Polynomial.C (93/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (603/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-10819/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (20231/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-73099/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (19892/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (27371/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-4281/1190 : ℚ)*Polynomial.X^10 + Polynomial.C (-38839/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (29829/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (12503/13685 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf0766.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0766.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0766.rational a+Real.sqrt 2*evalQPoly rf0766.irrational a)/evalQPoly rf0766.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0766,rf0747]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (179/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-1777/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (1579/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (49/1564 : ℚ)*Polynomial.X^6 + Polynomial.C (-213/805 : ℚ)*Polynomial.X^7 + Polynomial.C (36517/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-2393/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-207/952 : ℚ)*Polynomial.X^10 + Polynomial.C (653/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-147/3910 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf0785.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0785.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0785.rational a+Real.sqrt 2*evalQPoly rf0785.irrational a)/evalQPoly rf0785.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0785,rf0747]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-64/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (4467/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-16798/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1231/595 : ℚ)*Polynomial.X^7 + Polynomial.C (-1816/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-36149/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (3481/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-251/1610 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf0812.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0812.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0812.rational a+Real.sqrt 2*evalQPoly rf0812.irrational a)/evalQPoly rf0812.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0812,rf0747]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (3/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^3 + Polynomial.C (-403/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (3327/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-1773/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (27389/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-37664/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (7639/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (63919/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-73363/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-10993/13685 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf0794.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0794.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0794.rational a+Real.sqrt 2*evalQPoly rf0794.irrational a)/evalQPoly rf0794.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0794,rf0747]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-169/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2607/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-4147/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (4272/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (231/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-105013/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (25252/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-1192/1955 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf0821.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0821.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0821.rational a+Real.sqrt 2*evalQPoly rf0821.irrational a)/evalQPoly rf0821.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0821,rf0747]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (909/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-6437/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (17579/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-961/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-8433/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (12072/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (104/161 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf0838.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0838.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0838.rational a+Real.sqrt 2*evalQPoly rf0838.irrational a)/evalQPoly rf0838.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0838,rf0747]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (11/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (7/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-804/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (3776/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-618/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-11777/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (27884/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (97/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-43/35 : ℚ)*Polynomial.X^10 + Polynomial.C (-4241/3910 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf0830.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0830.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0830.rational a+Real.sqrt 2*evalQPoly rf0830.irrational a)/evalQPoly rf0830.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0830,rf0747]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (11/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-163/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1059/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-2868/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (771/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (1349/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-407/805 : ℚ)*Polynomial.X^9 + Polynomial.C (457/1955 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf0847.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0847.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0847.rational a+Real.sqrt 2*evalQPoly rf0847.irrational a)/evalQPoly rf0847.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0847,rf0747]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0747.eval a
  | 0,1 => -rf0757.eval a
  | 0,2 => -rf0776.eval a
  | 0,3 => -rf0803.eval a
  | 1,0 => -rf0766.eval a
  | 1,1 => -rf0785.eval a
  | 1,2 => -rf0812.eval a
  | 2,0 => -rf0794.eval a
  | 2,1 => -rf0821.eval a
  | 2,2 => -rf0838.eval a
  | 3,0 => -rf0830.eval a
  | 3,1 => -rf0847.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (2,0,1) i j := by
  intro i j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hbase : evalQPoly rf0747.denominator a≠0 := h0
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
  all_goals norm_num [evalQPoly,den,rf0747,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (2,0,1) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn4 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0)]

theorem raw_column_4 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn4 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn4,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_4

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0747,rf0757,rf0766,rf0013,rf0776,rf0785,rf0794,rf0013,rf0803,rf0013,rf0812,rf0821,rf0830,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0838,rf0847,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0747.DefinedAt a) (h1 : rf0757.DefinedAt a) (h2 : rf0776.DefinedAt a) (h3 : rf0803.DefinedAt a) (h4 : rf0766.DefinedAt a) (h5 : rf0785.DefinedAt a) (h6 : rf0812.DefinedAt a) (h7 : rf0794.DefinedAt a) (h8 : rf0821.DefinedAt a) (h9 : rf0838.DefinedAt a) (h10 : rf0830.DefinedAt a) (h11 : rf0847.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (2,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even008
