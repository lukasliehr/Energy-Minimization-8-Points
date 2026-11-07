import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd036
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1535.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/28 : ℚ)*Polynomial.X^1 + Polynomial.C (1 : ℚ)*Polynomial.X^2 + Polynomial.C (-89/28 : ℚ)*Polynomial.X^3 + Polynomial.C (29/14 : ℚ)*Polynomial.X^4 + Polynomial.C (263/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-118/7 : ℚ)*Polynomial.X^6 + Polynomial.C (61/28 : ℚ)*Polynomial.X^7 + Polynomial.C (61/14 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1535.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1535.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1535.rational a+Real.sqrt 2*evalQPoly rf1535.irrational a)/evalQPoly rf1535.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1535,rf1535]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^3 + Polynomial.C (61/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-11/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-33/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1550.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1550.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1550.rational a+Real.sqrt 2*evalQPoly rf1550.irrational a)/evalQPoly rf1550.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1550,rf1535]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (5/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/7 : ℚ)*Polynomial.X^3 + Polynomial.C (117/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-7/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1578.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1578.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1578.rational a+Real.sqrt 2*evalQPoly rf1578.irrational a)/evalQPoly rf1578.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1578,rf1535]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^1 + Polynomial.C (23/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-67/28 : ℚ)*Polynomial.X^3 + Polynomial.C (17/4 : ℚ)*Polynomial.X^4 + Polynomial.C (71/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-631/28 : ℚ)*Polynomial.X^6 + Polynomial.C (523/28 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1564.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1564.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1564.rational a+Real.sqrt 2*evalQPoly rf1564.irrational a)/evalQPoly rf1564.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1564,rf1535]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/28 : ℚ)*Polynomial.X^2 + Polynomial.C (13/7 : ℚ)*Polynomial.X^3 + Polynomial.C (19/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-57/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-1/28 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1592.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1592.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1592.rational a+Real.sqrt 2*evalQPoly rf1592.irrational a)/evalQPoly rf1592.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1592,rf1535]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (81/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-6 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1621.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1621.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1621.rational a+Real.sqrt 2*evalQPoly rf1621.irrational a)/evalQPoly rf1621.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1621,rf1535]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/28 : ℚ)*Polynomial.X^2 + Polynomial.C (27/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-11/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-60/7 : ℚ)*Polynomial.X^5 + Polynomial.C (391/28 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1606.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1606.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1606.rational a+Real.sqrt 2*evalQPoly rf1606.irrational a)/evalQPoly rf1606.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1606,rf1535]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (8/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-53/14 : ℚ)*Polynomial.X^4 + Polynomial.C (6/7 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1635.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1635.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1635.rational a+Real.sqrt 2*evalQPoly rf1635.irrational a)/evalQPoly rf1635.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1635,rf1535]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (7/2 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1647.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1647.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1647.rational a+Real.sqrt 2*evalQPoly rf1647.irrational a)/evalQPoly rf1647.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1647,rf1535]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd036
