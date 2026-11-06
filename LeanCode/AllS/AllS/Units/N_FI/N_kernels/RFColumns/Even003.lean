import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even003
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf0742.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (-123/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (185/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-1523/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-59813/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (33449/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-340912/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (3209977/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-9732651/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (5193169/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-2234781/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (1610097/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-542035/21896 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf0742.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0742.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0742.rational a+Real.sqrt 2*evalQPoly rf0742.irrational a)/evalQPoly rf0742.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0742,rf0742]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (97/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (11/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (-31107/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (17139/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-6795/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (384/805 : ℚ)*Polynomial.X^8 + Polynomial.C (138375/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (-412103/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (15439/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (-112823/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (235/272 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf0752.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0752.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0752.rational a+Real.sqrt 2*evalQPoly rf0752.irrational a)/evalQPoly rf0752.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0752,rf0742]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (6/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-883/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-94/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (4081/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-87222/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (622529/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-142862/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (36137/476 : ℚ)*Polynomial.X^10 + Polynomial.C (-876828/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (15581/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf0771.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0771.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0771.rational a+Real.sqrt 2*evalQPoly rf0771.irrational a)/evalQPoly rf0771.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0771,rf0742]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-33/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (81/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-5293/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (66/391 : ℚ)*Polynomial.X^8 + Polynomial.C (19699/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-17601/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (25/92 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf0799.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0799.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0799.rational a+Real.sqrt 2*evalQPoly rf0799.irrational a)/evalQPoly rf0799.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0799,rf0742]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/595 : ℚ)*Polynomial.X^2 + Polynomial.C (-559/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-439/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (18129/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-15210/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (570643/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-94458/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (1458525/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-32229/805 : ℚ)*Polynomial.X^10 + Polynomial.C (-1256807/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (149721/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-623513/21896 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf0761.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0761.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0761.rational a+Real.sqrt 2*evalQPoly rf0761.irrational a)/evalQPoly rf0761.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0761,rf0742]
  all_goals ring

def n5 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (43/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (1731/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-4119/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (3147/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-26562/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (11299/9520 : ℚ)*Polynomial.X^8 + Polynomial.C (52439/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-47529/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (43203/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-22477/6256 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf0780.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0780.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0780.rational a+Real.sqrt 2*evalQPoly rf0780.irrational a)/evalQPoly rf0780.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0780,rf0742]
  all_goals ring

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^2 + Polynomial.C (13/1564 : ℚ)*Polynomial.X^3 + Polynomial.C (422/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-20357/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (65519/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-92065/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (70106/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-2533497/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (53309/1610 : ℚ)*Polynomial.X^10 + Polynomial.C (-6409/644 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf0807.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0807.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0807.rational a+Real.sqrt 2*evalQPoly rf0807.irrational a)/evalQPoly rf0807.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0807,rf0742]
  all_goals ring

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1564 : ℚ)*Polynomial.X^2 + Polynomial.C (79/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-981/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-6899/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (69089/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-309933/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (871051/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-3398347/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (922653/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-3956097/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (325251/10948 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf0789.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0789.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0789.rational a+Real.sqrt 2*evalQPoly rf0789.irrational a)/evalQPoly rf0789.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0789,rf0742]
  all_goals ring

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (9/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-373/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-29/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (1767/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-12429/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (537/2380 : ℚ)*Polynomial.X^7 + Polynomial.C (16257/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-252449/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (723/460 : ℚ)*Polynomial.X^10 + Polynomial.C (-1155/3128 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf0816.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0816.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0816.rational a+Real.sqrt 2*evalQPoly rf0816.irrational a)/evalQPoly rf0816.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0816,rf0742]
  all_goals ring

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/595 : ℚ)*Polynomial.X^3 + Polynomial.C (-652/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2789/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-80289/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (246524/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-442328/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (178613/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-4705/322 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf0834.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0834.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0834.rational a+Real.sqrt 2*evalQPoly rf0834.irrational a)/evalQPoly rf0834.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0834,rf0742]
  all_goals ring

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (29/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (984/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-11981/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (51284/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-92313/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-3112/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (19869/782 : ℚ)*Polynomial.X^9 + Polynomial.C (-32554/805 : ℚ)*Polynomial.X^10 + Polynomial.C (17485/782 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf0825.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0825.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf0825.rational a+Real.sqrt 2*evalQPoly rf0825.irrational a)/evalQPoly rf0825.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf0825,rf0742]
  all_goals ring

def n11 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (33/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (19/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-45/1564 : ℚ)*Polynomial.X^4 + Polynomial.C (4773/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-3237/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (33/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (159853/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-110893/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (2551/3128 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf0842.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0842.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0842.rational a+Real.sqrt 2*evalQPoly rf0842.irrational a)/evalQPoly rf0842.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0842,rf0742]
  all_goals ring

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf0742.eval a
  | 0,1 => -rf0752.eval a
  | 0,2 => -rf0771.eval a
  | 0,3 => -rf0799.eval a
  | 1,0 => -rf0761.eval a
  | 1,1 => -rf0780.eval a
  | 1,2 => -rf0807.eval a
  | 2,0 => -rf0789.eval a
  | 2,1 => -rf0816.eval a
  | 2,2 => -rf0834.eval a
  | 3,0 => -rf0825.eval a
  | 3,1 => -rf0842.eval a
  | _,_ => 0
theorem values (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    ∀ i j,(∑ r,vector a r*(parityFiberU a false i)^r.1.val*(parityFiberZ a false i j)^r.2.val)=paritySourceData a false (0,0,2) i j := by
  intro i j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hbase : evalQPoly rf0742.denominator a≠0 := h0
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
  all_goals norm_num [evalQPoly,den,rf0742,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,parityFiberZ,parityFiberU,parityFiberPair,parityFiberPairs,parityFiberLabel,paritySourceData,parityIndexLabel,parityMonomial,parityZ,parityW,parityFiberSize,evenFiberSizes,oddFiberSizes]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    ∀ r,parityKernelCoefficients a false (0,0,2) (parityIndexTag false r)=vector a r :=
  parity_coefficients_unique a ha _ _ _ (values a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

#print axioms coefficients

def rawColumn4 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0)]

theorem raw_column_4 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn4 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn4,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_4

def rawColumn5 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0)]

theorem raw_column_5 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn5 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn5,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_5

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn6 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn7 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn8 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0742,rf0752,rf0761,rf0013,rf0771,rf0780,rf0789,rf0013,rf0799,rf0013,rf0807,rf0816,rf0825,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0834,rf0842,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [parityMonomial (0,0,0),parityMonomial (0,1,0),parityMonomial (1,0,0),parityMonomial (0,0,1),parityMonomial (0,2,0),parityMonomial (1,1,0),parityMonomial (2,0,0),parityMonomial (0,1,1),parityMonomial (0,3,0),parityMonomial (1,0,1),parityMonomial (1,2,0),parityMonomial (2,1,0),parityMonomial (3,0,0),parityMonomial (0,0,2),parityMonomial (0,2,1),parityMonomial (0,4,0),parityMonomial (1,1,1),parityMonomial (1,3,0),parityMonomial (2,0,1),parityMonomial (2,2,0),parityMonomial (3,1,0),parityMonomial (4,0,0),parityMonomial (0,1,2),parityMonomial (0,3,1),parityMonomial (0,5,0),parityMonomial (1,0,2),parityMonomial (1,2,1),parityMonomial (1,4,0),parityMonomial (2,1,1),parityMonomial (2,3,0),parityMonomial (3,0,1),parityMonomial (3,2,0),parityMonomial (4,1,0),parityMonomial (5,0,0),parityMonomial (0,0,3),parityMonomial (0,2,2),parityMonomial (0,4,1),parityMonomial (0,6,0),parityMonomial (1,1,2),parityMonomial (1,3,1),parityMonomial (1,5,0),parityMonomial (2,0,2),parityMonomial (2,2,1),parityMonomial (2,4,0),parityMonomial (3,1,1),parityMonomial (3,3,0),parityMonomial (4,0,1),parityMonomial (4,2,0),parityMonomial (5,1,0),parityMonomial (6,0,0),parityMonomial (0,1,3),parityMonomial (0,3,2),parityMonomial (0,5,1),parityMonomial (0,7,0),parityMonomial (1,0,3),parityMonomial (1,2,2),parityMonomial (1,4,1),parityMonomial (1,6,0),parityMonomial (2,1,2),parityMonomial (2,3,1),parityMonomial (2,5,0),parityMonomial (3,0,2),parityMonomial (3,2,1),parityMonomial (3,4,0),parityMonomial (4,1,1),parityMonomial (4,3,0),parityMonomial (5,0,1),parityMonomial (5,2,0),parityMonomial (6,1,0),parityMonomial (7,0,0),parityMonomial (0,0,4),parityMonomial (0,2,3),parityMonomial (0,4,2),parityMonomial (0,6,1),parityMonomial (0,8,0),parityMonomial (1,1,3),parityMonomial (1,3,2),parityMonomial (1,5,1),parityMonomial (1,7,0),parityMonomial (2,0,3),parityMonomial (2,2,2),parityMonomial (2,4,1),parityMonomial (2,6,0),parityMonomial (3,1,2),parityMonomial (3,3,1),parityMonomial (3,5,0),parityMonomial (4,0,2),parityMonomial (4,2,1),parityMonomial (4,4,0),parityMonomial (5,1,1),parityMonomial (5,3,0),parityMonomial (6,0,1),parityMonomial (6,2,0),parityMonomial (7,1,0),parityMonomial (8,0,0),parityMonomial (0,1,4),parityMonomial (0,3,3),parityMonomial (0,5,2),parityMonomial (0,7,1),parityMonomial (0,9,0),parityMonomial (1,0,4),parityMonomial (1,2,3),parityMonomial (1,4,2),parityMonomial (1,6,1),parityMonomial (1,8,0),parityMonomial (2,1,3),parityMonomial (2,3,2),parityMonomial (2,5,1),parityMonomial (2,7,0),parityMonomial (3,0,3),parityMonomial (3,2,2),parityMonomial (3,4,1),parityMonomial (3,6,0),parityMonomial (4,1,2),parityMonomial (4,3,1),parityMonomial (4,5,0),parityMonomial (5,0,2),parityMonomial (5,2,1),parityMonomial (5,4,0),parityMonomial (6,1,1),parityMonomial (6,3,0),parityMonomial (7,0,1),parityMonomial (7,2,0),parityMonomial (8,1,0),parityMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0742.DefinedAt a) (h1 : rf0752.DefinedAt a) (h2 : rf0771.DefinedAt a) (h3 : rf0799.DefinedAt a) (h4 : rf0761.DefinedAt a) (h5 : rf0780.DefinedAt a) (h6 : rf0807.DefinedAt a) (h7 : rf0789.DefinedAt a) (h8 : rf0816.DefinedAt a) (h9 : rf0834.DefinedAt a) (h10 : rf0825.DefinedAt a) (h11 : rf0842.DefinedAt a) :
    rawColumn9 a=parityKernelFeature false a (0,0,2) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [parity_feature_expansion_indexed a ha]
  simp_rw [coefficients a ha h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,parity_sum_even,parityIndexTag,parityFiberSize,evenFiberSizes,oddFiberSizes,parityMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Even003
