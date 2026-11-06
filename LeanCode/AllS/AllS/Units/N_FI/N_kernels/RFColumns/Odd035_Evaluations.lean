import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd035
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1534.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (3/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^3 + Polynomial.C (6/35 : ℚ)*Polynomial.X^4 + Polynomial.C (11/10 : ℚ)*Polynomial.X^5 + Polynomial.C (-87/35 : ℚ)*Polynomial.X^6 + Polynomial.C (179/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^8 + Polynomial.C (-101/28 : ℚ)*Polynomial.X^9 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1534.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1534.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1534.rational a+Real.sqrt 2*evalQPoly rf1534.irrational a)/evalQPoly rf1534.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1534,rf1534]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^3 + Polynomial.C (1/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^5 + Polynomial.C (79/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1 : ℚ)*Polynomial.X^7 + Polynomial.C (-11/70 : ℚ)*Polynomial.X^8 + Polynomial.C (27/140 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1549.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1549.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1549.rational a+Real.sqrt 2*evalQPoly rf1549.irrational a)/evalQPoly rf1549.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1549,rf1534]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^2 + Polynomial.C (9/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-36/35 : ℚ)*Polynomial.X^5 + Polynomial.C (73/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1577.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1577.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1577.rational a+Real.sqrt 2*evalQPoly rf1577.irrational a)/evalQPoly rf1577.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1577,rf1534]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (69/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-123/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/20 : ℚ)*Polynomial.X^4 + Polynomial.C (499/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-629/140 : ℚ)*Polynomial.X^6 + Polynomial.C (723/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-857/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-29/140 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1563.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1563.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1563.rational a+Real.sqrt 2*evalQPoly rf1563.irrational a)/evalQPoly rf1563.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1563,rf1534]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^3 + Polynomial.C (1/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^5 + Polynomial.C (187/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-19/7 : ℚ)*Polynomial.X^7 + Polynomial.C (19/70 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf1591.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1591.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1591.rational a+Real.sqrt 2*evalQPoly rf1591.irrational a)/evalQPoly rf1591.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1591,rf1534]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-51/140 : ℚ)*Polynomial.X^2 + Polynomial.C (1/4 : ℚ)*Polynomial.X^3 + Polynomial.C (121/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-173/140 : ℚ)*Polynomial.X^5 + Polynomial.C (347/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf1620.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1620.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1620.rational a+Real.sqrt 2*evalQPoly rf1620.irrational a)/evalQPoly rf1620.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1620,rf1534]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/35 : ℚ)*Polynomial.X^3 + Polynomial.C (33/70 : ℚ)*Polynomial.X^4 + Polynomial.C (6/7 : ℚ)*Polynomial.X^5 + Polynomial.C (41/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-26/7 : ℚ)*Polynomial.X^7 + Polynomial.C (19/70 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1605.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1605.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1605.rational a+Real.sqrt 2*evalQPoly rf1605.irrational a)/evalQPoly rf1605.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1605,rf1534]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (17/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/5 : ℚ)*Polynomial.X^4 + Polynomial.C (79/70 : ℚ)*Polynomial.X^5 + Polynomial.C (26/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-113/70 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf1634.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1634.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1634.rational a+Real.sqrt 2*evalQPoly rf1634.irrational a)/evalQPoly rf1634.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1634,rf1534]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-51/140 : ℚ)*Polynomial.X^2 + Polynomial.C (1/4 : ℚ)*Polynomial.X^3 + Polynomial.C (121/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-173/140 : ℚ)*Polynomial.X^5 + Polynomial.C (347/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1620.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1620.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1620.rational a+Real.sqrt 2*evalQPoly rf1620.irrational a)/evalQPoly rf1620.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1620,rf1534]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd035
