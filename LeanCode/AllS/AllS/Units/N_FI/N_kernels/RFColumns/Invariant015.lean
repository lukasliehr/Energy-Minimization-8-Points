import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Invariant015
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0149.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/460 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/115 : ℚ)*Polynomial.X^2 + Polynomial.C (-91/920 : ℚ)*Polynomial.X^3 + Polynomial.C (141/92 : ℚ)*Polynomial.X^4 + Polynomial.C (-140/23 : ℚ)*Polynomial.X^5 + Polynomial.C (1002/115 : ℚ)*Polynomial.X^6 + Polynomial.C (1933/920 : ℚ)*Polynomial.X^7 + Polynomial.C (-8023/460 : ℚ)*Polynomial.X^8 + Polynomial.C (773/46 : ℚ)*Polynomial.X^9 + Polynomial.C (-1727/230 : ℚ)*Polynomial.X^10 + Polynomial.C (134/115 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf0142.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0142.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0142.rational a+Real.sqrt 2*evalQPoly rf0142.irrational a)/evalQPoly rf0142.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0142,rf0149]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (1/460 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/460 : ℚ)*Polynomial.X^1 + Polynomial.C (-101/920 : ℚ)*Polynomial.X^2 + Polynomial.C (1291/920 : ℚ)*Polynomial.X^3 + Polynomial.C (-2239/460 : ℚ)*Polynomial.X^4 + Polynomial.C (237/46 : ℚ)*Polynomial.X^5 + Polynomial.C (3991/920 : ℚ)*Polynomial.X^6 + Polynomial.C (-1217/184 : ℚ)*Polynomial.X^7 + Polynomial.C (-987/92 : ℚ)*Polynomial.X^8 + Polynomial.C (3961/230 : ℚ)*Polynomial.X^9 + Polynomial.C (-211/23 : ℚ)*Polynomial.X^10 + Polynomial.C (134/115 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf0149.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0149.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0149.rational a+Real.sqrt 2*evalQPoly rf0149.irrational a)/evalQPoly rf0149.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0149,rf0149]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (1/460 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/920 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/8 : ℚ)*Polynomial.X^2 + Polynomial.C (147/115 : ℚ)*Polynomial.X^3 + Polynomial.C (-463/115 : ℚ)*Polynomial.X^4 + Polynomial.C (3329/920 : ℚ)*Polynomial.X^5 + Polynomial.C (7353/920 : ℚ)*Polynomial.X^6 + Polynomial.C (-9761/460 : ℚ)*Polynomial.X^7 + Polynomial.C (647/46 : ℚ)*Polynomial.X^8 + Polynomial.C (-363/230 : ℚ)*Polynomial.X^9 + Polynomial.C (-383/230 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf0156.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0156.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0156.rational a+Real.sqrt 2*evalQPoly rf0156.irrational a)/evalQPoly rf0156.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0156,rf0149]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (3/920 : ℚ)*Polynomial.X^1 + Polynomial.C (3/46 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/92 : ℚ)*Polynomial.X^3 + Polynomial.C (707/920 : ℚ)*Polynomial.X^4 + Polynomial.C (-1013/920 : ℚ)*Polynomial.X^5 + Polynomial.C (1887/460 : ℚ)*Polynomial.X^6 + Polynomial.C (-209/23 : ℚ)*Polynomial.X^7 + Polynomial.C (1989/230 : ℚ)*Polynomial.X^8 + Polynomial.C (-689/230 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf0163.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0163.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0163.rational a+Real.sqrt 2*evalQPoly rf0163.irrational a)/evalQPoly rf0163.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0163,rf0149]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (1/460 : ℚ)*Polynomial.X^1 + Polynomial.C (7/92 : ℚ)*Polynomial.X^2 + Polynomial.C (-44/115 : ℚ)*Polynomial.X^3 + Polynomial.C (271/920 : ℚ)*Polynomial.X^4 + Polynomial.C (329/460 : ℚ)*Polynomial.X^5 + Polynomial.C (-48/115 : ℚ)*Polynomial.X^6 + Polynomial.C (-79/230 : ℚ)*Polynomial.X^7 + Polynomial.C (77/230 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf0170.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0170.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0170.rational a+Real.sqrt 2*evalQPoly rf0170.irrational a)/evalQPoly rf0170.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0170,rf0149]
  all_goals ring

def vector (a : ℝ) : Fin 5 → ℝ := ![-rf0142.eval a,-rf0149.eval a,-rf0156.eval a,-rf0163.eval a,-rf0170.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    ∀ r,∑ i,vector a i*(contactSigma a r)^i.val=orbitData a (invariantMonomial (3,0,1)) r := by
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
  all_goals norm_num [evalQPoly,den,rf0149,n0,n1,n2,n3,n4,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    invariantKernelCoefficients a (3,0,1)=vector a :=
  invariant_coefficients_unique a ha _ _ (values a ha h0 h1 h2 h3 h4)

#print axioms coefficients

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0142,rf0149,rf0013,rf0156,rf0013,rf0013,rf0163,rf0013,rf0013,rf0013,rf0170,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    rawColumn6 a=invariantKernelFeature a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0142,rf0149,rf0013,rf0156,rf0013,rf0013,rf0163,rf0013,rf0013,rf0013,rf0170,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    rawColumn7 a=invariantKernelFeature a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0142,rf0149,rf0013,rf0156,rf0013,rf0013,rf0163,rf0013,rf0013,rf0013,rf0170,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    rawColumn8 a=invariantKernelFeature a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0142,rf0149,rf0013,rf0156,rf0013,rf0013,rf0163,rf0013,rf0013,rf0013,rf0170,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0),invariantMonomial (0,0,3),invariantMonomial (0,3,1),invariantMonomial (1,1,2),invariantMonomial (1,4,0),invariantMonomial (2,2,1),invariantMonomial (3,0,2),invariantMonomial (3,3,0),invariantMonomial (4,1,1),invariantMonomial (5,2,0),invariantMonomial (6,0,1),invariantMonomial (7,1,0),invariantMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0142.DefinedAt a) (h1 : rf0149.DefinedAt a) (h2 : rf0156.DefinedAt a) (h3 : rf0163.DefinedAt a) (h4 : rf0170.DefinedAt a) :
    rawColumn9 a=invariantKernelFeature a (3,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Invariant015
