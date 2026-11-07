import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd038
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1537.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (7/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-8 : ℚ)*Polynomial.X^3 + Polynomial.C (10 : ℚ)*Polynomial.X^4 + Polynomial.C (-15/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-11/2 : ℚ)*Polynomial.X^6
theorem eval0 (a : ℝ) (h : rf1537.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1537.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1537.rational a+Real.sqrt 2*evalQPoly rf1537.irrational a)/evalQPoly rf1537.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1537,rf1537]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/4 : ℚ)*Polynomial.X^0 + Polynomial.C (5/4 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (4 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^5
theorem eval1 (a : ℝ) (h : rf1552.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1552.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1552.rational a+Real.sqrt 2*evalQPoly rf1552.irrational a)/evalQPoly rf1552.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1552,rf1537]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/4 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^2 + Polynomial.C (3 : ℚ)*Polynomial.X^3 + Polynomial.C (7/4 : ℚ)*Polynomial.X^4
theorem eval2 (a : ℝ) (h : rf1580.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1580.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1580.rational a+Real.sqrt 2*evalQPoly rf1580.irrational a)/evalQPoly rf1580.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1580,rf1537]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-4 : ℚ)*Polynomial.X^3 + Polynomial.C (12 : ℚ)*Polynomial.X^4 + Polynomial.C (-24 : ℚ)*Polynomial.X^5
theorem eval3 (a : ℝ) (h : rf1566.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1566.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1566.rational a+Real.sqrt 2*evalQPoly rf1566.irrational a)/evalQPoly rf1566.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1566,rf1537]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (7 : ℚ)*Polynomial.X^3 + Polynomial.C (-5 : ℚ)*Polynomial.X^4
theorem eval4 (a : ℝ) (h : rf1594.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1594.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1594.rational a+Real.sqrt 2*evalQPoly rf1594.irrational a)/evalQPoly rf1594.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1594,rf1537]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2 : ℚ)*Polynomial.X^1 + Polynomial.C (-4 : ℚ)*Polynomial.X^2 + Polynomial.C (6 : ℚ)*Polynomial.X^3
theorem eval5 (a : ℝ) (h : rf1623.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1623.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1623.rational a+Real.sqrt 2*evalQPoly rf1623.irrational a)/evalQPoly rf1623.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1623,rf1537]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-5 : ℚ)*Polynomial.X^2 + Polynomial.C (15 : ℚ)*Polynomial.X^3 + Polynomial.C (-19 : ℚ)*Polynomial.X^4
theorem eval6 (a : ℝ) (h : rf1608.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1608.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1608.rational a+Real.sqrt 2*evalQPoly rf1608.irrational a)/evalQPoly rf1608.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1608,rf1537]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (7/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^3
theorem eval7 (a : ℝ) (h : rf1637.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1637.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1637.rational a+Real.sqrt 2*evalQPoly rf1637.irrational a)/evalQPoly rf1637.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1637,rf1537]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (4 : ℚ)*Polynomial.X^2 + Polynomial.C (-4 : ℚ)*Polynomial.X^3
theorem eval8 (a : ℝ) (h : rf1191.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1191.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1191.rational a+Real.sqrt 2*evalQPoly rf1191.irrational a)/evalQPoly rf1191.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1191,rf1537]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd038
