import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd031
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1530.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (73/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-93/7 : ℚ)*Polynomial.X^3 + Polynomial.C (155/14 : ℚ)*Polynomial.X^4 + Polynomial.C (19/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^6 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-15/14 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1530.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1530.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1530.rational a+Real.sqrt 2*evalQPoly rf1530.irrational a)/evalQPoly rf1530.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1530,rf1530]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (47/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-45/14 : ℚ)*Polynomial.X^2 + Polynomial.C (107/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-67/7 : ℚ)*Polynomial.X^4 + Polynomial.C (461/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-97/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-183/28 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1545.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1545.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1545.rational a+Real.sqrt 2*evalQPoly rf1545.irrational a)/evalQPoly rf1545.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1545,rf1530]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (12/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-40/7 : ℚ)*Polynomial.X^3 + Polynomial.C (58/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-2 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1573.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1573.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1573.rational a+Real.sqrt 2*evalQPoly rf1573.irrational a)/evalQPoly rf1573.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1573,rf1530]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/14 : ℚ)*Polynomial.X^1 + Polynomial.C (32/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-209/14 : ℚ)*Polynomial.X^3 + Polynomial.C (131/7 : ℚ)*Polynomial.X^4 + Polynomial.C (29/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-95/14 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1559.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1559.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1559.rational a+Real.sqrt 2*evalQPoly rf1559.irrational a)/evalQPoly rf1559.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1559,rf1530]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (13/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-117/28 : ℚ)*Polynomial.X^2 + Polynomial.C (39/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-297/28 : ℚ)*Polynomial.X^4 + Polynomial.C (51/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-739/28 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1587.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1587.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1587.rational a+Real.sqrt 2*evalQPoly rf1587.irrational a)/evalQPoly rf1587.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1587,rf1530]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-3/7 : ℚ)*Polynomial.X^0 + Polynomial.C (19/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-22/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-50/7 : ℚ)*Polynomial.X^3 + Polynomial.C (15 : ℚ)*Polynomial.X^4 + Polynomial.C (-7 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1616.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1616.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1616.rational a+Real.sqrt 2*evalQPoly rf1616.irrational a)/evalQPoly rf1616.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1616,rf1530]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-43/7 : ℚ)*Polynomial.X^2 + Polynomial.C (90/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-66/7 : ℚ)*Polynomial.X^4 + Polynomial.C (102/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-85/7 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1601.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1601.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1601.rational a+Real.sqrt 2*evalQPoly rf1601.irrational a)/evalQPoly rf1601.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1601,rf1530]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (4/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/14 : ℚ)*Polynomial.X^1 + Polynomial.C (18/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-33/7 : ℚ)*Polynomial.X^3 + Polynomial.C (86/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-183/14 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1630.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1630.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1630.rational a+Real.sqrt 2*evalQPoly rf1630.irrational a)/evalQPoly rf1630.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1630,rf1530]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^2 + Polynomial.C (2 : ℚ)*Polynomial.X^3 + Polynomial.C (27/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-4 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1644.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1644.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1644.rational a+Real.sqrt 2*evalQPoly rf1644.irrational a)/evalQPoly rf1644.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1644,rf1530]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd031
