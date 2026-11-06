import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd026
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1525.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/140 : ℚ)*Polynomial.X^1 + Polynomial.C (23/140 : ℚ)*Polynomial.X^2 + Polynomial.C (1/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-487/140 : ℚ)*Polynomial.X^4 + Polynomial.C (1583/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-273/20 : ℚ)*Polynomial.X^6 + Polynomial.C (761/140 : ℚ)*Polynomial.X^7 + Polynomial.C (199/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-47/7 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1525.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1525.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1525.rational a+Real.sqrt 2*evalQPoly rf1525.irrational a)/evalQPoly rf1525.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1525,rf1525]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-97/70 : ℚ)*Polynomial.X^3 + Polynomial.C (291/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-459/70 : ℚ)*Polynomial.X^5 + Polynomial.C (216/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-27/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-17/28 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1540.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1540.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1540.rational a+Real.sqrt 2*evalQPoly rf1540.irrational a)/evalQPoly rf1540.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1540,rf1525]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (1/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/140 : ℚ)*Polynomial.X^3 + Polynomial.C (121/140 : ℚ)*Polynomial.X^4 + Polynomial.C (53/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-57/20 : ℚ)*Polynomial.X^6 + Polynomial.C (7/4 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1569.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1569.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1569.rational a+Real.sqrt 2*evalQPoly rf1569.irrational a)/evalQPoly rf1569.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1569,rf1525]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (31/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^4 + Polynomial.C (75/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-1879/70 : ℚ)*Polynomial.X^6 + Polynomial.C (1004/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-577/28 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1554.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1554.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1554.rational a+Real.sqrt 2*evalQPoly rf1554.irrational a)/evalQPoly rf1554.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1554,rf1525]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-23/35 : ℚ)*Polynomial.X^3 + Polynomial.C (148/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-69/7 : ℚ)*Polynomial.X^5 + Polynomial.C (64/5 : ℚ)*Polynomial.X^6 + Polynomial.C (-45/7 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1582.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1582.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1582.rational a+Real.sqrt 2*evalQPoly rf1582.irrational a)/evalQPoly rf1582.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1582,rf1525]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^3 + Polynomial.C (81/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-13/35 : ℚ)*Polynomial.X^5 + Polynomial.C (3/2 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1611.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1611.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1611.rational a+Real.sqrt 2*evalQPoly rf1611.irrational a)/evalQPoly rf1611.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1611,rf1525]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/20 : ℚ)*Polynomial.X^3 + Polynomial.C (89/20 : ℚ)*Polynomial.X^4 + Polynomial.C (-307/28 : ℚ)*Polynomial.X^5 + Polynomial.C (263/20 : ℚ)*Polynomial.X^6 + Polynomial.C (-229/28 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1596.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1596.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1596.rational a+Real.sqrt 2*evalQPoly rf1596.irrational a)/evalQPoly rf1596.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1596,rf1525]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/70 : ℚ)*Polynomial.X^2 + Polynomial.C (74/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-69/14 : ℚ)*Polynomial.X^4 + Polynomial.C (32/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-45/14 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1625.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1625.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1625.rational a+Real.sqrt 2*evalQPoly rf1625.irrational a)/evalQPoly rf1625.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1625,rf1525]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^2 + Polynomial.C (4/35 : ℚ)*Polynomial.X^3 + Polynomial.C (4/5 : ℚ)*Polynomial.X^4 + Polynomial.C (3/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1639.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1639.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1639.rational a+Real.sqrt 2*evalQPoly rf1639.irrational a)/evalQPoly rf1639.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1639,rf1525]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd026
