import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd034
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1533.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/14 : ℚ)*Polynomial.X^2 + Polynomial.C (211/28 : ℚ)*Polynomial.X^3 + Polynomial.C (1/2 : ℚ)*Polynomial.X^4 + Polynomial.C (-997/28 : ℚ)*Polynomial.X^5 + Polynomial.C (705/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-183/28 : ℚ)*Polynomial.X^7 + Polynomial.C (-193/14 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1533.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1533.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1533.rational a+Real.sqrt 2*evalQPoly rf1533.irrational a)/evalQPoly rf1533.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1533,rf1533]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-1 : ℚ)*Polynomial.X^1 + Polynomial.C (12/7 : ℚ)*Polynomial.X^2 + Polynomial.C (18/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-81/7 : ℚ)*Polynomial.X^4 + Polynomial.C (83/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-22/7 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1548.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1548.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1548.rational a+Real.sqrt 2*evalQPoly rf1548.irrational a)/evalQPoly rf1548.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1548,rf1533]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-1 : ℚ)*Polynomial.X^1 + Polynomial.C (10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (20/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-7 : ℚ)*Polynomial.X^4 + Polynomial.C (11/7 : ℚ)*Polynomial.X^5 + Polynomial.C (2 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1576.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1576.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1576.rational a+Real.sqrt 2*evalQPoly rf1576.irrational a)/evalQPoly rf1576.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1576,rf1533]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (9/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-65/28 : ℚ)*Polynomial.X^2 + Polynomial.C (257/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-279/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-793/28 : ℚ)*Polynomial.X^5 + Polynomial.C (2281/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-1537/28 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1562.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1562.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1562.rational a+Real.sqrt 2*evalQPoly rf1562.irrational a)/evalQPoly rf1562.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1562,rf1533]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (20/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-76/7 : ℚ)*Polynomial.X^4 + Polynomial.C (160/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-88/7 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1590.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1590.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1590.rational a+Real.sqrt 2*evalQPoly rf1590.irrational a)/evalQPoly rf1590.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1590,rf1533]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/7 : ℚ)*Polynomial.X^1 + Polynomial.C (20/7 : ℚ)*Polynomial.X^2 + Polynomial.C (16/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-11 : ℚ)*Polynomial.X^4 + Polynomial.C (7 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1619.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1619.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1619.rational a+Real.sqrt 2*evalQPoly rf1619.irrational a)/evalQPoly rf1619.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1619,rf1533]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/28 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (13/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-45/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-233/28 : ℚ)*Polynomial.X^4 + Polynomial.C (205/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-751/28 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1604.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1604.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1604.rational a+Real.sqrt 2*evalQPoly rf1604.irrational a)/evalQPoly rf1604.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1604,rf1533]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (10/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^3 + Polynomial.C (80/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-44/7 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1633.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1633.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1633.rational a+Real.sqrt 2*evalQPoly rf1633.irrational a)/evalQPoly rf1633.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1633,rf1533]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (6/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-51/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1646.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1646.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1646.rational a+Real.sqrt 2*evalQPoly rf1646.irrational a)/evalQPoly rf1646.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1646,rf1533]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd034
