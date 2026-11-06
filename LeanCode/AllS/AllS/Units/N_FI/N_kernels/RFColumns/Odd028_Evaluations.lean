import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd028
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1527.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-155/14 : ℚ)*Polynomial.X^3 + Polynomial.C (1489/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-3153/14 : ℚ)*Polynomial.X^5 + Polynomial.C (2591/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-361/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-123/2 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1527.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1527.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1527.rational a+Real.sqrt 2*evalQPoly rf1527.irrational a)/evalQPoly rf1527.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1527,rf1527]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (17/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-317/28 : ℚ)*Polynomial.X^2 + Polynomial.C (1471/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-2657/28 : ℚ)*Polynomial.X^4 + Polynomial.C (2039/28 : ℚ)*Polynomial.X^5 + Polynomial.C (45/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-81/4 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1542.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1542.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1542.rational a+Real.sqrt 2*evalQPoly rf1542.irrational a)/evalQPoly rf1542.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1542,rf1527]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (3/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^1 + Polynomial.C (1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (11 : ℚ)*Polynomial.X^3 + Polynomial.C (-43/4 : ℚ)*Polynomial.X^4 + Polynomial.C (1/2 : ℚ)*Polynomial.X^5 + Polynomial.C (7/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1571.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1571.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1571.rational a+Real.sqrt 2*evalQPoly rf1571.irrational a)/evalQPoly rf1571.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1571,rf1527]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (10/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-55/7 : ℚ)*Polynomial.X^2 + Polynomial.C (75/7 : ℚ)*Polynomial.X^3 + Polynomial.C (508/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-2060/7 : ℚ)*Polynomial.X^5 + Polynomial.C (2813/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-239 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1556.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1556.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1556.rational a+Real.sqrt 2*evalQPoly rf1556.irrational a)/evalQPoly rf1556.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1556,rf1527]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/7 : ℚ)*Polynomial.X^2 + Polynomial.C (42 : ℚ)*Polynomial.X^3 + Polynomial.C (-886/7 : ℚ)*Polynomial.X^4 + Polynomial.C (1179/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-81 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1584.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1584.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1584.rational a+Real.sqrt 2*evalQPoly rf1584.irrational a)/evalQPoly rf1584.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1584,rf1527]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1 : ℚ)*Polynomial.X^0 + Polynomial.C (-5 : ℚ)*Polynomial.X^1 + Polynomial.C (2 : ℚ)*Polynomial.X^2 + Polynomial.C (14 : ℚ)*Polynomial.X^3 + Polynomial.C (-19 : ℚ)*Polynomial.X^4 + Polynomial.C (7 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1613.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1613.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1613.rational a+Real.sqrt 2*evalQPoly rf1613.irrational a)/evalQPoly rf1613.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1613,rf1527]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-5/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (37/7 : ℚ)*Polynomial.X^2 + Polynomial.C (228/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-129 : ℚ)*Polynomial.X^4 + Polynomial.C (1312/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-95 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1598.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1598.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1598.rational a+Real.sqrt 2*evalQPoly rf1598.irrational a)/evalQPoly rf1598.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1598,rf1527]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-17/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (21 : ℚ)*Polynomial.X^2 + Polynomial.C (-443/7 : ℚ)*Polynomial.X^3 + Polynomial.C (1179/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-81/2 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1627.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1627.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1627.rational a+Real.sqrt 2*evalQPoly rf1627.irrational a)/evalQPoly rf1627.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1627,rf1527]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/7 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (30/7 : ℚ)*Polynomial.X^2 + Polynomial.C (2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (5/7 : ℚ)*Polynomial.X^4 + Polynomial.C (13 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1641.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1641.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1641.rational a+Real.sqrt 2*evalQPoly rf1641.irrational a)/evalQPoly rf1641.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1641,rf1527]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd028
