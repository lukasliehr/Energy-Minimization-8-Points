import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd060
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1327.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^1 + Polynomial.C (23/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-18 : ℚ)*Polynomial.X^3 + Polynomial.C (57/2 : ℚ)*Polynomial.X^4 + Polynomial.C (-79/4 : ℚ)*Polynomial.X^5 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^6 + Polynomial.C (11/2 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf1327.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1327.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1327.rational a+Real.sqrt 2*evalQPoly rf1327.irrational a)/evalQPoly rf1327.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1327,rf1327]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := 0
theorem eval1 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0013,rf1327]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := 0
theorem eval2 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0013,rf1327]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (3/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-23/4 : ℚ)*Polynomial.X^1 + Polynomial.C (81/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-85/2 : ℚ)*Polynomial.X^3 + Polynomial.C (227/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-183/4 : ℚ)*Polynomial.X^5 + Polynomial.C (73/4 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1363.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1363.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1363.rational a+Real.sqrt 2*evalQPoly rf1363.irrational a)/evalQPoly rf1363.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1363,rf1327]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := 0
theorem eval4 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf0013,rf1327]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf1327]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (9/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-23/2 : ℚ)*Polynomial.X^3 + Polynomial.C (29/2 : ℚ)*Polynomial.X^4 + Polynomial.C (-7 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1417.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1417.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1417.rational a+Real.sqrt 2*evalQPoly rf1417.irrational a)/evalQPoly rf1417.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1417,rf1327]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := 0
theorem eval7 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf0013,rf1327]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-7/4 : ℚ)*Polynomial.X^0 + Polynomial.C (19/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-51/2 : ℚ)*Polynomial.X^2 + Polynomial.C (65/2 : ℚ)*Polynomial.X^3 + Polynomial.C (-71/4 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf1488.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1488.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1488.rational a+Real.sqrt 2*evalQPoly rf1488.irrational a)/evalQPoly rf1488.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1488,rf1327]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd060
