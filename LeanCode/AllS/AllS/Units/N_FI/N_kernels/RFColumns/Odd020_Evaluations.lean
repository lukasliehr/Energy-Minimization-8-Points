import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd020
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1227.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (15/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-18/7 : ℚ)*Polynomial.X^4 + Polynomial.C (93/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-127/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-43/7 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf1227.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1227.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1227.rational a+Real.sqrt 2*evalQPoly rf1227.irrational a)/evalQPoly rf1227.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1227,rf1227]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (57/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-13/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-11/7 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf1238.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1238.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1238.rational a+Real.sqrt 2*evalQPoly rf1238.irrational a)/evalQPoly rf1238.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1238,rf1227]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (25/14 : ℚ)*Polynomial.X^4 + Polynomial.C (1 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf1258.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1258.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1258.rational a+Real.sqrt 2*evalQPoly rf1258.irrational a)/evalQPoly rf1258.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1258,rf1227]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (11/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-4 : ℚ)*Polynomial.X^3 + Polynomial.C (2 : ℚ)*Polynomial.X^4 + Polynomial.C (114/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-323/14 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1247.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1247.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1247.rational a+Real.sqrt 2*evalQPoly rf1247.irrational a)/evalQPoly rf1247.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1247,rf1227]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (36/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-44/7 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf1267.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1267.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1267.rational a+Real.sqrt 2*evalQPoly rf1267.irrational a)/evalQPoly rf1267.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1267,rf1227]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-2 : ℚ)*Polynomial.X^3 + Polynomial.C (7/2 : ℚ)*Polynomial.X^4
theorem eval5 (a : ℝ) (h : rf1286.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1286.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1286.rational a+Real.sqrt 2*evalQPoly rf1286.irrational a)/evalQPoly rf1286.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1286,rf1227]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^2 + Polynomial.C (10/7 : ℚ)*Polynomial.X^3 + Polynomial.C (107/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-44/7 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1277.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1277.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1277.rational a+Real.sqrt 2*evalQPoly rf1277.irrational a)/evalQPoly rf1277.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1277,rf1227]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (24/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-51/14 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf1296.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1296.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1296.rational a+Real.sqrt 2*evalQPoly rf1296.irrational a)/evalQPoly rf1296.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1296,rf1227]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^2 + Polynomial.C (12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (5/2 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf1306.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1306.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1306.rational a+Real.sqrt 2*evalQPoly rf1306.irrational a)/evalQPoly rf1306.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1306,rf1227]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd020
