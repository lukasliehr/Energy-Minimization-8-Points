import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Sign015
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0600.denominator
def n0 : Polynomial ℚ := Polynomial.C (1/8 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^1 + Polynomial.C (33/8 : ℚ)*Polynomial.X^2 + Polynomial.C (-35/2 : ℚ)*Polynomial.X^3 + Polynomial.C (391/8 : ℚ)*Polynomial.X^4 + Polynomial.C (-283/4 : ℚ)*Polynomial.X^5 + Polynomial.C (343/8 : ℚ)*Polynomial.X^6
theorem eval0 (a : ℝ) (h : rf0600.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0600.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0600.rational a+Real.sqrt 2*evalQPoly rf0600.irrational a)/evalQPoly rf0600.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0600,rf0600]
  all_goals ring

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-12 : ℚ)*Polynomial.X^2 + Polynomial.C (41 : ℚ)*Polynomial.X^3 + Polynomial.C (-64 : ℚ)*Polynomial.X^4 + Polynomial.C (79/2 : ℚ)*Polynomial.X^5
theorem eval1 (a : ℝ) (h : rf0607.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0607.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0607.rational a+Real.sqrt 2*evalQPoly rf0607.irrational a)/evalQPoly rf0607.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0607,rf0600]
  all_goals ring

def vector (a : ℝ) : Fin 2 → ℝ := ![-rf0600.eval a,-rf0607.eval a]
theorem values (a : ℝ) (ha : physical a) (h0 : rf0600.DefinedAt a) (h1 : rf0607.DefinedAt a) :
    ∀ r,∑ i,vector a i*(signSigmaNodes a r)^i.val=orbitData a (invariantMonomial (0,3,0)) (regularOrbit r) := by
  intro r
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
  simp only [vector,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,eval0 a h0 hD,eval1 a h1 hD]
  field_simp [hD]
  fin_cases r
  all_goals norm_num [evalQPoly,den,rf0600,n0,n1,contactSigma_values,orbitData,invariantMonomial,sigma,e2,e3,standardContactPoint,contactTripleEval,contactRepresentative,contacts,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Fin.castAdd,Fin.castLE,div_eq_mul_inv,hi,signSigmaNodes,regularOrbit]
  all_goals field_simp
  all_goals try ring_nf
  all_goals try simp only [hs,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs19,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,hs28,hs29,hs30,hs31,hs32]
  all_goals ring

theorem coefficients (a : ℝ) (ha : physical a) (h0 : rf0600.DefinedAt a) (h1 : rf0607.DefinedAt a) :
    signKernelCoefficients a (0,3,0)=vector a :=
  sign_coefficients_unique a ha _ _ (values a ha h0 h1)

#print axioms coefficients

def rawColumn9 (a : ℝ) : Poly3 :=
  rfRawColumn a [rf0600,rf0607,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0013,rf0012,rf0013,rf0013,rf0013,rf0013,rf0013]
    [deltaPoly*invariantMonomial (0,0,0),deltaPoly*invariantMonomial (1,0,0),deltaPoly*invariantMonomial (0,1,0),deltaPoly*invariantMonomial (2,0,0),deltaPoly*invariantMonomial (0,0,1),deltaPoly*invariantMonomial (1,1,0),deltaPoly*invariantMonomial (3,0,0),deltaPoly*invariantMonomial (0,2,0),deltaPoly*invariantMonomial (1,0,1),deltaPoly*invariantMonomial (2,1,0),deltaPoly*invariantMonomial (4,0,0),deltaPoly*invariantMonomial (0,1,1),deltaPoly*invariantMonomial (1,2,0),deltaPoly*invariantMonomial (2,0,1),deltaPoly*invariantMonomial (3,1,0),deltaPoly*invariantMonomial (5,0,0),deltaPoly*invariantMonomial (0,0,2),deltaPoly*invariantMonomial (0,3,0),deltaPoly*invariantMonomial (1,1,1),deltaPoly*invariantMonomial (2,2,0),deltaPoly*invariantMonomial (3,0,1),deltaPoly*invariantMonomial (4,1,0),deltaPoly*invariantMonomial (6,0,0)]

theorem raw_column_9 (a : ℝ) (ha : physical a) (h0 : rf0600.DefinedAt a) (h1 : rf0607.DefinedAt a) :
    rawColumn9 a=signKernelFeature a (0,3,0) := by
  have h12 : rf0012.eval a=1 := by norm_num [rf0012,RatFun.eval,evalQPoly]
  have h13 : rf0013.eval a=0 := by norm_num [rf0013,RatFun.eval,evalQPoly]
  rw [signKernelFeature_expansion a ha,coefficients a ha h0 h1]
  all_goals simp [rawColumn9,rfRawColumn,h12,h13,Fin.sum_univ_succ,vector,invariantMonomial]
  all_goals ring
#print axioms raw_column_9

end Blueprint.Thomson.Finite.RFColumnProofs.Sign015
