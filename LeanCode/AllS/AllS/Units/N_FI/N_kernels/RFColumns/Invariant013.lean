import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Invariant013
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0147.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/920 : ℚ)*Polynomial.X^1 + Polynomial.C (7/460 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (-341/460 : ℚ)*Polynomial.X^4 + Polynomial.C (11787/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (-22561/920 : ℚ)*Polynomial.X^6 + Polynomial.C (92327/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (-5892/115 : ℚ)*Polynomial.X^8 + Polynomial.C (27639/1840 : ℚ)*Polynomial.X^9 + Polynomial.C (8973/920 : ℚ)*Polynomial.X^10 + Polynomial.C (-731/230 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf0140.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0140.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0140.rational a+Real.sqrt 2*evalQPoly rf0140.irrational a)/evalQPoly rf0140.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0140,rf0147]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (13/920 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/1840 : ℚ)*Polynomial.X^2 + Polynomial.C (-1343/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (2157/368 : ℚ)*Polynomial.X^4 + Polynomial.C (-38607/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (70351/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-10473/368 : ℚ)*Polynomial.X^7 + Polynomial.C (-12883/1840 : ℚ)*Polynomial.X^8 + Polynomial.C (26481/1840 : ℚ)*Polynomial.X^9 + Polynomial.C (2593/920 : ℚ)*Polynomial.X^10 + Polynomial.C (37/115 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf0147.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0147.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0147.rational a+Real.sqrt 2*evalQPoly rf0147.irrational a)/evalQPoly rf0147.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0147,rf0147]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (1/80 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/1840 : ℚ)*Polynomial.X^2 + Polynomial.C (-239/368 : ℚ)*Polynomial.X^3 + Polynomial.C (77/16 : ℚ)*Polynomial.X^4 + Polynomial.C (-31397/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (61577/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-61057/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (13959/1840 : ℚ)*Polynomial.X^8 + Polynomial.C (8221/920 : ℚ)*Polynomial.X^9 + Polynomial.C (-263/460 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf0154.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0154.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0154.rational a+Real.sqrt 2*evalQPoly rf0154.irrational a)/evalQPoly rf0154.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0154,rf0147]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (1/1840 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/1840 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/368 : ℚ)*Polynomial.X^2 + Polynomial.C (599/1840 : ℚ)*Polynomial.X^3 + Polynomial.C (-2907/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (6129/1840 : ℚ)*Polynomial.X^5 + Polynomial.C (-4723/1840 : ℚ)*Polynomial.X^6 + Polynomial.C (-1523/1840 : ℚ)*Polynomial.X^7 + Polynomial.C (1427/920 : ℚ)*Polynomial.X^8 + Polynomial.C (-99/460 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf0161.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0161.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0161.rational a+Real.sqrt 2*evalQPoly rf0161.irrational a)/evalQPoly rf0161.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0161,rf0147]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (1/1840 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/230 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/1840 : ℚ)*Polynomial.X^2 + Polynomial.C (269/920 : ℚ)*Polynomial.X^3 + Polynomial.C (-2349/1840 : ℚ)*Polynomial.X^4 + Polynomial.C (1069/460 : ℚ)*Polynomial.X^5 + Polynomial.C (-101/80 : ℚ)*Polynomial.X^6 + Polynomial.C (-499/920 : ℚ)*Polynomial.X^7 + Polynomial.C (-33/460 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf0168.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0168.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0168.rational a+Real.sqrt 2*evalQPoly rf0168.irrational a)/evalQPoly rf0168.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0168,rf0147]
  all_goals ring

def vector (a : ℝ) : Fin 5 → ℝ := ![-rf0140.eval a,-rf0147.eval a,-rf0154.eval a,-rf0161.eval a,-rf0168.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    ∀ r,∑ i,vector a i*(contactSigma a r)^i.val=orbitData a (invariantMonomial (1,1,1)) r := by
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
  all_goals norm_num [evalQPoly,den,rf0147,n0,n1,n2,n3,n4,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    invariantKernelCoefficients a (1,1,1)=vector a :=
  invariant_coefficients_unique a ha _ _ (values a ha h0 h1 h2 h3 h4)

#print axioms coefficients

def rawColumn6 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0140,rf0147,rf0013,rf0154,rf0013,rf0013,rf0161,rf0013,rf0013,rf0013,rf0168,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0)]

theorem raw_column_6 (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    rawColumn6 a=invariantKernelFeature a (1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn6,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_6

def rawColumn7 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0140,rf0147,rf0013,rf0154,rf0013,rf0013,rf0161,rf0013,rf0013,rf0013,rf0168,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0)]

theorem raw_column_7 (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    rawColumn7 a=invariantKernelFeature a (1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn7,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_7

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0140,rf0147,rf0013,rf0154,rf0013,rf0013,rf0161,rf0013,rf0013,rf0013,rf0168,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    rawColumn8 a=invariantKernelFeature a (1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0140,rf0147,rf0013,rf0154,rf0013,rf0013,rf0161,rf0013,rf0013,rf0013,rf0168,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0),invariantMonomial (0,0,3),invariantMonomial (0,3,1),invariantMonomial (1,1,2),invariantMonomial (1,4,0),invariantMonomial (2,2,1),invariantMonomial (3,0,2),invariantMonomial (3,3,0),invariantMonomial (4,1,1),invariantMonomial (5,2,0),invariantMonomial (6,0,1),invariantMonomial (7,1,0),invariantMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0140.DefinedAt a) (h1 : rf0147.DefinedAt a) (h2 : rf0154.DefinedAt a) (h3 : rf0161.DefinedAt a) (h4 : rf0168.DefinedAt a) :
    rawColumn9 a=invariantKernelFeature a (1,1,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Invariant013
