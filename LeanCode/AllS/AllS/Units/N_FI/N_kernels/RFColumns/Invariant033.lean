import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Invariant033
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0391.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/460 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/115 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/8 : ℚ)*Polynomial.X^3 + Polynomial.C (853/460 : ℚ)*Polynomial.X^4 + Polynomial.C (-327/46 : ℚ)*Polynomial.X^5 + Polynomial.C (1327/230 : ℚ)*Polynomial.X^6 + Polynomial.C (30301/920 : ℚ)*Polynomial.X^7 + Polynomial.C (-56431/460 : ℚ)*Polynomial.X^8 + Polynomial.C (26003/115 : ℚ)*Polynomial.X^9 + Polynomial.C (-30986/115 : ℚ)*Polynomial.X^10 + Polynomial.C (22654/115 : ℚ)*Polynomial.X^11 + Polynomial.C (-8714/115 : ℚ)*Polynomial.X^12 + Polynomial.C (1224/115 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf0381.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0381.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0381.rational a+Real.sqrt 2*evalQPoly rf0381.irrational a)/evalQPoly rf0381.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0381,rf0391]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (1/460 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/460 : ℚ)*Polynomial.X^1 + Polynomial.C (-25/184 : ℚ)*Polynomial.X^2 + Polynomial.C (311/184 : ℚ)*Polynomial.X^3 + Polynomial.C (-2541/460 : ℚ)*Polynomial.X^4 + Polynomial.C (152/115 : ℚ)*Polynomial.X^5 + Polynomial.C (28051/920 : ℚ)*Polynomial.X^6 + Polynomial.C (-12829/184 : ℚ)*Polynomial.X^7 + Polynomial.C (21647/460 : ℚ)*Polynomial.X^8 + Polynomial.C (8113/115 : ℚ)*Polynomial.X^9 + Polynomial.C (-48559/230 : ℚ)*Polynomial.X^10 + Polynomial.C (48981/230 : ℚ)*Polynomial.X^11 + Polynomial.C (-10398/115 : ℚ)*Polynomial.X^12 + Polynomial.C (1224/115 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf0391.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0391.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0391.rational a+Real.sqrt 2*evalQPoly rf0391.irrational a)/evalQPoly rf0391.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0391,rf0391]
  all_goals ring

def n2 : Polynomial ℚ := Polynomial.C (1/460 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/920 : ℚ)*Polynomial.X^1 + Polynomial.C (-147/920 : ℚ)*Polynomial.X^2 + Polynomial.C (381/230 : ℚ)*Polynomial.X^3 + Polynomial.C (-1149/230 : ℚ)*Polynomial.X^4 + Polynomial.C (-1123/920 : ℚ)*Polynomial.X^5 + Polynomial.C (47381/920 : ℚ)*Polynomial.X^6 + Polynomial.C (-77987/460 : ℚ)*Polynomial.X^7 + Polynomial.C (33873/115 : ℚ)*Polynomial.X^8 + Polynomial.C (-34929/115 : ℚ)*Polynomial.X^9 + Polynomial.C (17869/115 : ℚ)*Polynomial.X^10 + Polynomial.C (-1203/115 : ℚ)*Polynomial.X^11 + Polynomial.C (-1684/115 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf0401.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0401.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0401.rational a+Real.sqrt 2*evalQPoly rf0401.irrational a)/evalQPoly rf0401.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0401,rf0391]
  all_goals ring

def n3 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (3/920 : ℚ)*Polynomial.X^1 + Polynomial.C (17/230 : ℚ)*Polynomial.X^2 + Polynomial.C (-209/460 : ℚ)*Polynomial.X^3 + Polynomial.C (671/920 : ℚ)*Polynomial.X^4 + Polynomial.C (-1121/920 : ℚ)*Polynomial.X^5 + Polynomial.C (5481/460 : ℚ)*Polynomial.X^6 + Polynomial.C (-2347/46 : ℚ)*Polynomial.X^7 + Polynomial.C (13059/115 : ℚ)*Polynomial.X^8 + Polynomial.C (-16511/115 : ℚ)*Polynomial.X^9 + Polynomial.C (22177/230 : ℚ)*Polynomial.X^10 + Polynomial.C (-6079/230 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf0411.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0411.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0411.rational a+Real.sqrt 2*evalQPoly rf0411.irrational a)/evalQPoly rf0411.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0411,rf0391]
  all_goals ring

def n4 : Polynomial ℚ := Polynomial.C (-1/920 : ℚ)*Polynomial.X^0 + Polynomial.C (1/460 : ℚ)*Polynomial.X^1 + Polynomial.C (43/460 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^3 + Polynomial.C (227/920 : ℚ)*Polynomial.X^4 + Polynomial.C (1209/460 : ℚ)*Polynomial.X^5 + Polynomial.C (-807/115 : ℚ)*Polynomial.X^6 + Polynomial.C (1391/115 : ℚ)*Polynomial.X^7 + Polynomial.C (-281/23 : ℚ)*Polynomial.X^8 + Polynomial.C (643/115 : ℚ)*Polynomial.X^9 + Polynomial.C (-74/115 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf0421.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0421.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0421.rational a+Real.sqrt 2*evalQPoly rf0421.irrational a)/evalQPoly rf0421.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0421,rf0391]
  all_goals ring

def vector (a : ℝ) : Fin 5 → ℝ := ![-rf0381.eval a,-rf0391.eval a,-rf0401.eval a,-rf0411.eval a,-rf0421.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0381.DefinedAt a) (h1 : rf0391.DefinedAt a) (h2 : rf0401.DefinedAt a) (h3 : rf0411.DefinedAt a) (h4 : rf0421.DefinedAt a) :
    ∀ r,∑ i,vector a i*(contactSigma a r)^i.val=orbitData a (invariantMonomial (5,0,1)) r := by
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
  all_goals norm_num [evalQPoly,den,rf0391,n0,n1,n2,n3,n4,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0381.DefinedAt a) (h1 : rf0391.DefinedAt a) (h2 : rf0401.DefinedAt a) (h3 : rf0411.DefinedAt a) (h4 : rf0421.DefinedAt a) :
    invariantKernelCoefficients a (5,0,1)=vector a :=
  invariant_coefficients_unique a ha _ _ (values a ha h0 h1 h2 h3 h4)

#print axioms coefficients

def rawColumn8 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0381,rf0391,rf0013,rf0401,rf0013,rf0013,rf0411,rf0013,rf0013,rf0013,rf0421,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0)]

theorem raw_column_8 (a : ℝ) (ha : physical a) (h0 : rf0381.DefinedAt a) (h1 : rf0391.DefinedAt a) (h2 : rf0401.DefinedAt a) (h3 : rf0411.DefinedAt a) (h4 : rf0421.DefinedAt a) :
    rawColumn8 a=invariantKernelFeature a (5,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn8,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_8

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0381,rf0391,rf0013,rf0401,rf0013,rf0013,rf0411,rf0013,rf0013,rf0013,rf0421,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013]
    [invariantMonomial (0,0,0),invariantMonomial (1,0,0),invariantMonomial (0,1,0),invariantMonomial (2,0,0),invariantMonomial (0,0,1),invariantMonomial (1,1,0),invariantMonomial (3,0,0),invariantMonomial (0,2,0),invariantMonomial (1,0,1),invariantMonomial (2,1,0),invariantMonomial (4,0,0),invariantMonomial (0,1,1),invariantMonomial (1,2,0),invariantMonomial (2,0,1),invariantMonomial (3,1,0),invariantMonomial (5,0,0),invariantMonomial (0,0,2),invariantMonomial (0,3,0),invariantMonomial (1,1,1),invariantMonomial (2,2,0),invariantMonomial (3,0,1),invariantMonomial (4,1,0),invariantMonomial (6,0,0),invariantMonomial (0,2,1),invariantMonomial (1,0,2),invariantMonomial (1,3,0),invariantMonomial (2,1,1),invariantMonomial (3,2,0),invariantMonomial (4,0,1),invariantMonomial (5,1,0),invariantMonomial (7,0,0),invariantMonomial (0,1,2),invariantMonomial (0,4,0),invariantMonomial (1,2,1),invariantMonomial (2,0,2),invariantMonomial (2,3,0),invariantMonomial (3,1,1),invariantMonomial (4,2,0),invariantMonomial (5,0,1),invariantMonomial (6,1,0),invariantMonomial (8,0,0),invariantMonomial (0,0,3),invariantMonomial (0,3,1),invariantMonomial (1,1,2),invariantMonomial (1,4,0),invariantMonomial (2,2,1),invariantMonomial (3,0,2),invariantMonomial (3,3,0),invariantMonomial (4,1,1),invariantMonomial (5,2,0),invariantMonomial (6,0,1),invariantMonomial (7,1,0),invariantMonomial (9,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0381.DefinedAt a) (h1 : rf0391.DefinedAt a) (h2 : rf0401.DefinedAt a) (h3 : rf0411.DefinedAt a) (h4 : rf0421.DefinedAt a) :
    rawColumn9 a=invariantKernelFeature a (5,0,1) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [invariantKernelFeature_expansion a ha,coefficients a ha h0 h1 h2 h3 h4]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Invariant033
