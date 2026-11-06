import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd013
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1220.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (9/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-169/35 : ℚ)*Polynomial.X^4 + Polynomial.C (321/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-1553/35 : ℚ)*Polynomial.X^6 + Polynomial.C (2601/70 : ℚ)*Polynomial.X^7 + Polynomial.C (73/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-335/14 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1220.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1220.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1220.rational a+Real.sqrt 2*evalQPoly rf1220.irrational a)/evalQPoly rf1220.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1220,rf1220]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (61/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-59/14 : ℚ)*Polynomial.X^3 + Polynomial.C (21/2 : ℚ)*Polynomial.X^4 + Polynomial.C (-199/14 : ℚ)*Polynomial.X^5 + Polynomial.C (587/70 : ℚ)*Polynomial.X^6 + Polynomial.C (207/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-59/14 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1231.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1231.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1231.rational a+Real.sqrt 2*evalQPoly rf1231.irrational a)/evalQPoly rf1231.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1231,rf1220]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (18/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-141/70 : ℚ)*Polynomial.X^3 + Polynomial.C (76/35 : ℚ)*Polynomial.X^4 + Polynomial.C (283/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-438/35 : ℚ)*Polynomial.X^6 + Polynomial.C (23/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1251.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1251.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1251.rational a+Real.sqrt 2*evalQPoly rf1251.irrational a)/evalQPoly rf1251.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1251,rf1220]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (107/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-174/35 : ℚ)*Polynomial.X^3 + Polynomial.C (9/2 : ℚ)*Polynomial.X^4 + Polynomial.C (108/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-161/2 : ℚ)*Polynomial.X^6 + Polynomial.C (4042/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-530/7 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1240.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1240.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1240.rational a+Real.sqrt 2*evalQPoly rf1240.irrational a)/evalQPoly rf1240.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1240,rf1220]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^3 + Polynomial.C (76/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-752/35 : ℚ)*Polynomial.X^5 + Polynomial.C (842/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-76/7 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1260.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1260.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1260.rational a+Real.sqrt 2*evalQPoly rf1260.irrational a)/evalQPoly rf1260.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1260,rf1220]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (6/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/70 : ℚ)*Polynomial.X^2 + Polynomial.C (4/5 : ℚ)*Polynomial.X^3 + Polynomial.C (57/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-138/35 : ℚ)*Polynomial.X^5 + Polynomial.C (13/2 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1279.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1279.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1279.rational a+Real.sqrt 2*evalQPoly rf1279.irrational a)/evalQPoly rf1279.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1279,rf1220]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/70 : ℚ)*Polynomial.X^3 + Polynomial.C (344/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-1877/70 : ℚ)*Polynomial.X^5 + Polynomial.C (1248/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-299/14 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1270.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1270.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1270.rational a+Real.sqrt 2*evalQPoly rf1270.irrational a)/evalQPoly rf1270.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1270,rf1220]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (38/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-376/35 : ℚ)*Polynomial.X^4 + Polynomial.C (421/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1289.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1289.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1289.rational a+Real.sqrt 2*evalQPoly rf1289.irrational a)/evalQPoly rf1289.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1289,rf1220]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/70 : ℚ)*Polynomial.X^2 + Polynomial.C (64/35 : ℚ)*Polynomial.X^3 + Polynomial.C (29/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-272/35 : ℚ)*Polynomial.X^5 + Polynomial.C (17/2 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1299.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1299.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1299.rational a+Real.sqrt 2*evalQPoly rf1299.irrational a)/evalQPoly rf1299.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1299,rf1220]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd013
