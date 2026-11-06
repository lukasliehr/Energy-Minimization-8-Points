import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd039
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1538.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-7 : ℚ)*Polynomial.X^3 + Polynomial.C (11 : ℚ)*Polynomial.X^4 + Polynomial.C (-5 : ℚ)*Polynomial.X^5 + Polynomial.C (-9/2 : ℚ)*Polynomial.X^6
theorem eval0 (a : ℝ) (h : rf1538.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1538.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1538.rational a+Real.sqrt 2*evalQPoly rf1538.irrational a)/evalQPoly rf1538.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1538,rf1538]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/4 : ℚ)*Polynomial.X^1 + Polynomial.C (-1 : ℚ)*Polynomial.X^2 + Polynomial.C (2 : ℚ)*Polynomial.X^3 + Polynomial.C (-2 : ℚ)*Polynomial.X^4 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^5
theorem eval1 (a : ℝ) (h : rf1381.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1381.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1381.rational a+Real.sqrt 2*evalQPoly rf1381.irrational a)/evalQPoly rf1381.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1381,rf1538]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := 0
theorem eval2 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0013,rf1538]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (7 : ℚ)*Polynomial.X^2 + Polynomial.C (-17 : ℚ)*Polynomial.X^3 + Polynomial.C (21 : ℚ)*Polynomial.X^4 + Polynomial.C (-27/2 : ℚ)*Polynomial.X^5
theorem eval3 (a : ℝ) (h : rf1567.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1567.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1567.rational a+Real.sqrt 2*evalQPoly rf1567.irrational a)/evalQPoly rf1567.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1567,rf1538]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/4 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^2 + Polynomial.C (5 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/4 : ℚ)*Polynomial.X^4
theorem eval4 (a : ℝ) (h : rf1452.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1452.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1452.rational a+Real.sqrt 2*evalQPoly rf1452.irrational a)/evalQPoly rf1452.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1452,rf1538]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf1538]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3 : ℚ)*Polynomial.X^2 + Polynomial.C (-8 : ℚ)*Polynomial.X^3 + Polynomial.C (9 : ℚ)*Polynomial.X^4
theorem eval6 (a : ℝ) (h : rf1609.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1609.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1609.rational a+Real.sqrt 2*evalQPoly rf1609.irrational a)/evalQPoly rf1609.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1609,rf1538]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (7/2 : ℚ)*Polynomial.X^3
theorem eval7 (a : ℝ) (h : rf1506.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1506.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1506.rational a+Real.sqrt 2*evalQPoly rf1506.irrational a)/evalQPoly rf1506.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1506,rf1538]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3 : ℚ)*Polynomial.X^1 + Polynomial.C (-8 : ℚ)*Polynomial.X^2 + Polynomial.C (9 : ℚ)*Polynomial.X^3
theorem eval8 (a : ℝ) (h : rf1649.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1649.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1649.rational a+Real.sqrt 2*evalQPoly rf1649.irrational a)/evalQPoly rf1649.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1649,rf1538]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd039
