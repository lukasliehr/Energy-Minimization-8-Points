import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Invariant014
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0148.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/920 : ℚ)*Polynomial.X^1 + Polynomial.C (3/115 : ℚ)*Polynomial.X^2 + Polynomial.C (-67/368 : ℚ)*Polynomial.X^3 + Polynomial.C (-83/920 : ℚ)*Polynomial.X^4 + Polynomial.C (13159/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (-17931/460 : ℚ)*Polynomial.X^6 + Polynomial.C (184503/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (-24991/184 : ℚ)*Polynomial.X^8 + Polynomial.C (33255/368 : ℚ)*Polynomial.X^9 + Polynomial.C (-5229/230 : ℚ)*Polynomial.X^10 + Polynomial.C (191/115 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf0141.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0141.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0141.rational a+Real.sqrt 2*evalQPoly rf0141.irrational a)/evalQPoly rf0141.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0141,rf0148]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-57/368 : ℚ)*Polynomial.X^2 + Polynomial.C (-481/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (12887/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (-60733/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (130377/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-117259/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (-11577/1840 : ℚ)*Polynomial.X^8 + Polynomial.C (76811/1840 : ℚ)*Polynomial.X^9 + Polynomial.C (-3081/230 : ℚ)*Polynomial.X^10 + Polynomial.C (191/115 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf0148.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0148.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0148.rational a+Real.sqrt 2*evalQPoly rf0148.irrational a)/evalQPoly rf0148.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0148,rf0148]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (47/1840 : ℚ)*Polynomial.X^1 + Polynomial.C (-63/368 : ℚ)*Polynomial.X^2 + Polynomial.C (-33/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (9849/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (-52407/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (131387/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-170123/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (93941/1840 : ℚ)*Polynomial.X^8 + Polynomial.C (-211/460 : ℚ)*Polynomial.X^9 + Polynomial.C (-1339/460 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf0155.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0155.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0155.rational a+Real.sqrt 2*evalQPoly rf0155.irrational a)/evalQPoly rf0155.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0155,rf0148]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (1/1840 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/1840 : ℚ)*Polynomial.X^1 + Polynomial.C (57/1840 : ℚ)*Polynomial.X^2 + Polynomial.C (613/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (-4573/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (10847/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (-6613/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-10817/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (1999/230 : ℚ)*Polynomial.X^8 + Polynomial.C (-343/115 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf0162.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0162.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0162.rational a+Real.sqrt 2*evalQPoly rf0162.irrational a)/evalQPoly rf0162.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0162,rf0148]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (1/1840 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/920 : ℚ)*Polynomial.X^1 + Polynomial.C (91/1840 : ℚ)*Polynomial.X^2 + Polynomial.C (117/460 : ℚ)*Polynomial.X^3 + Polynomial.C (-4313/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (5709/920 : ℚ)*Polynomial.X^5 + Polynomial.C (-12291/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (121/46 : ℚ)*Polynomial.X^7 + Polynomial.C (-76/115 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf0169.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0169.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0169.rational a+Real.sqrt 2*evalQPoly rf0169.irrational a)/evalQPoly rf0169.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0169,rf0148]
  all_goals ring

def vector (a : ℝ) : Fin 5 → ℝ := ![-rf0141.eval a,-rf0148.eval a,-rf0155.eval a,-rf0162.eval a,-rf0169.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    ∀ r,∑ i,vector a i*(contactSigma a r)^i.val=orbitData a (invariantMonomial (2,2,0)) r := by
  intro r
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h1
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
  simp only [vector,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD]
  field_simp [hD]
  fin_cases r
  all_goals norm_num [evalQPoly,den,rf0148,n0,n1,n2,n3,n4,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    invariantKernelCoefficients a (2,2,0)=vector a :=
  invariant_coefficients_unique a ha _ _ (values a ha h0 h1 h2 h3 h4)

#print axioms coefficients

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0141,rf0148,rf0013,rf0155,rf0013,rf0013,rf0162,rf0013,rf0013,rf0013,rf0169,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    rawColumn6 a=invariantKernelFeature a (2,2,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0141,rf0148,rf0013,rf0155,rf0013,rf0013,rf0162,rf0013,rf0013,rf0013,rf0169,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    rawColumn7 a=invariantKernelFeature a (2,2,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0141,rf0148,rf0013,rf0155,rf0013,rf0013,rf0162,rf0013,rf0013,rf0013,rf0169,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    rawColumn8 a=invariantKernelFeature a (2,2,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0141,rf0148,rf0013,rf0155,rf0013,rf0013,rf0162,rf0013,rf0013,rf0013,rf0169,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0),invariantMonomial (0,0,3),invariantMonomial (0,3,1),invariantMonomial (1,1,2),invariantMonomial (1,4,0),invariantMonomial (2,2,1),invariantMonomial (3,0,2),invariantMonomial (3,3,0),invariantMonomial (4,1,1),invariantMonomial (5,2,0),invariantMonomial (6,0,1),invariantMonomial (7,1,0),invariantMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0141.DefinedAt a) (h1 : rf0148.DefinedAt a) (h2 : rf0155.DefinedAt a) (h3 : rf0162.DefinedAt a) (h4 : rf0169.DefinedAt a) :
    rawColumn9 a=invariantKernelFeature a (2,2,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Invariant014
