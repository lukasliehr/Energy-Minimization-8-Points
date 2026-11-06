import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd024
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf0890.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (5/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^3 + Polynomial.C (1/2 : ℚ)*Polynomial.X^4 + Polynomial.C (1 : ℚ)*Polynomial.X^5
theorem eval0 (a : ℝ) (h : rf0890.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0890.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf0890.rational a+Real.sqrt 2*evalQPoly rf0890.irrational a)/evalQPoly rf0890.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf0890,rf0890]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := 0
theorem eval1 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0013,rf0890]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := 0
theorem eval2 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0013,rf0890]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^1 + Polynomial.C (5 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/2 : ℚ)*Polynomial.X^3 + Polynomial.C (7/2 : ℚ)*Polynomial.X^4
theorem eval3 (a : ℝ) (h : rf0910.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0910.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0910.rational a+Real.sqrt 2*evalQPoly rf0910.irrational a)/evalQPoly rf0910.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0910,rf0890]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := 0
theorem eval4 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0013,rf0890]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf0890]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1 : ℚ)*Polynomial.X^2 + Polynomial.C (-1 : ℚ)*Polynomial.X^3
theorem eval6 (a : ℝ) (h : rf0940.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0940.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0940.rational a+Real.sqrt 2*evalQPoly rf0940.irrational a)/evalQPoly rf0940.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0940,rf0890]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := 0
theorem eval7 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0013,rf0890]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/2 : ℚ)*Polynomial.X^0 + Polynomial.C (4 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/2 : ℚ)*Polynomial.X^2
theorem eval8 (a : ℝ) (h : rf0979.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0979.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0979.rational a+Real.sqrt 2*evalQPoly rf0979.irrational a)/evalQPoly rf0979.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0979,rf0890]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd024
