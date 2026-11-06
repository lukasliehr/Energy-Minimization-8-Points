import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd018
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1225.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (5/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/14 : ℚ)*Polynomial.X^2 + Polynomial.C (29/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-45/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-9/7 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf1225.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1225.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1225.rational a+Real.sqrt 2*evalQPoly rf1225.irrational a)/evalQPoly rf1225.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1225,rf1225]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (23/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-1 : ℚ)*Polynomial.X^5 + Polynomial.C (-8/7 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf1236.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1236.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1236.rational a+Real.sqrt 2*evalQPoly rf1236.irrational a)/evalQPoly rf1236.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1236,rf1225]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (20/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-1 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf1256.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1256.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1256.rational a+Real.sqrt 2*evalQPoly rf1256.irrational a)/evalQPoly rf1256.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1256,rf1225]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (5/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/14 : ℚ)*Polynomial.X^2 + Polynomial.C (36/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-45/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-79/14 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1245.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1245.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1245.rational a+Real.sqrt 2*evalQPoly rf1245.irrational a)/evalQPoly rf1245.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1245,rf1225]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (12/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^3 + Polynomial.C (36/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-32/7 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf1265.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1265.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1265.rational a+Real.sqrt 2*evalQPoly rf1265.irrational a)/evalQPoly rf1265.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1265,rf1225]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^1 + Polynomial.C (2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (34/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-4 : ℚ)*Polynomial.X^4
theorem eval5 (a : ℝ) (h : rf1284.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1284.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1284.rational a+Real.sqrt 2*evalQPoly rf1284.irrational a)/evalQPoly rf1284.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1284,rf1225]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (3 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/7 : ℚ)*Polynomial.X^3 + Polynomial.C (8/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-32/7 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1275.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1275.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1275.rational a+Real.sqrt 2*evalQPoly rf1275.irrational a)/evalQPoly rf1275.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1275,rf1225]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (6/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^2 + Polynomial.C (18/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-16/7 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf1294.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1294.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1294.rational a+Real.sqrt 2*evalQPoly rf1294.irrational a)/evalQPoly rf1294.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1294,rf1225]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (4/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf1304.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1304.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1304.rational a+Real.sqrt 2*evalQPoly rf1304.irrational a)/evalQPoly rf1304.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1304,rf1225]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd018
