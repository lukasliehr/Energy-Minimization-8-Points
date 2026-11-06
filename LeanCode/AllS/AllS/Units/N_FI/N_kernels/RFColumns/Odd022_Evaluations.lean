import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd022
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1229.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1 : ℚ)*Polynomial.X^2 + Polynomial.C (-7 : ℚ)*Polynomial.X^3 + Polynomial.C (9 : ℚ)*Polynomial.X^4 + Polynomial.C (5 : ℚ)*Polynomial.X^5
theorem eval0 (a : ℝ) (h : rf1229.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1229.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1229.rational a+Real.sqrt 2*evalQPoly rf1229.irrational a)/evalQPoly rf1229.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1229,rf1229]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^2 + Polynomial.C (1/2 : ℚ)*Polynomial.X^3 + Polynomial.C (1/2 : ℚ)*Polynomial.X^4
theorem eval1 (a : ℝ) (h : rf0426.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0426.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0426.rational a+Real.sqrt 2*evalQPoly rf0426.irrational a)/evalQPoly rf0426.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0426,rf1229]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (-1 : ℚ)*Polynomial.X^3
theorem eval2 (a : ℝ) (h : rf0173.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0173.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0173.rational a+Real.sqrt 2*evalQPoly rf0173.irrational a)/evalQPoly rf0173.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0173,rf1229]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (2 : ℚ)*Polynomial.X^2 + Polynomial.C (-8 : ℚ)*Polynomial.X^3 + Polynomial.C (18 : ℚ)*Polynomial.X^4
theorem eval3 (a : ℝ) (h : rf1249.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1249.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1249.rational a+Real.sqrt 2*evalQPoly rf1249.irrational a)/evalQPoly rf1249.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1249,rf1229]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (2 : ℚ)*Polynomial.X^3
theorem eval4 (a : ℝ) (h : rf1269.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1269.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1269.rational a+Real.sqrt 2*evalQPoly rf1269.irrational a)/evalQPoly rf1269.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1269,rf1229]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^2
theorem eval5 (a : ℝ) (h : rf1288.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1288.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1288.rational a+Real.sqrt 2*evalQPoly rf1288.irrational a)/evalQPoly rf1288.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1288,rf1229]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (2 : ℚ)*Polynomial.X^3
theorem eval6 (a : ℝ) (h : rf1269.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1269.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1269.rational a+Real.sqrt 2*evalQPoly rf1269.irrational a)/evalQPoly rf1269.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1269,rf1229]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1 : ℚ)*Polynomial.X^1 + Polynomial.C (1 : ℚ)*Polynomial.X^2
theorem eval7 (a : ℝ) (h : rf1298.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1298.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1298.rational a+Real.sqrt 2*evalQPoly rf1298.irrational a)/evalQPoly rf1298.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1298,rf1229]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-4 : ℚ)*Polynomial.X^2
theorem eval8 (a : ℝ) (h : rf0978.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0978.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0978.rational a+Real.sqrt 2*evalQPoly rf0978.irrational a)/evalQPoly rf0978.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0978,rf1229]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd022
