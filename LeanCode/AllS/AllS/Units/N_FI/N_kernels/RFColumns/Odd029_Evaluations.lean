import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd029
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1528.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (1/10 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/70 : ℚ)*Polynomial.X^3 + Polynomial.C (43/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-10 : ℚ)*Polynomial.X^5 + Polynomial.C (1443/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1409/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-311/70 : ℚ)*Polynomial.X^8 + Polynomial.C (2361/140 : ℚ)*Polynomial.X^9 + Polynomial.C (39/7 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1528.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1528.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1528.rational a+Real.sqrt 2*evalQPoly rf1528.irrational a)/evalQPoly rf1528.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1528,rf1528]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/70 : ℚ)*Polynomial.X^2 + Polynomial.C (82/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-179/35 : ℚ)*Polynomial.X^4 + Polynomial.C (487/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-57/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-68/35 : ℚ)*Polynomial.X^7 + Polynomial.C (261/140 : ℚ)*Polynomial.X^8 + Polynomial.C (15/28 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1543.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1543.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1543.rational a+Real.sqrt 2*evalQPoly rf1543.irrational a)/evalQPoly rf1543.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1543,rf1528]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^2 + Polynomial.C (69/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-223/70 : ℚ)*Polynomial.X^5 + Polynomial.C (95/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-317/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-13/4 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1572.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1572.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1572.rational a+Real.sqrt 2*evalQPoly rf1572.irrational a)/evalQPoly rf1572.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1572,rf1528]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (17/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/35 : ℚ)*Polynomial.X^2 + Polynomial.C (149/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-423/35 : ℚ)*Polynomial.X^5 + Polynomial.C (201/5 : ℚ)*Polynomial.X^6 + Polynomial.C (-4229/70 : ℚ)*Polynomial.X^7 + Polynomial.C (935/28 : ℚ)*Polynomial.X^8 + Polynomial.C (463/28 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1557.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1557.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1557.rational a+Real.sqrt 2*evalQPoly rf1557.irrational a)/evalQPoly rf1557.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1557,rf1528]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (64/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-377/70 : ℚ)*Polynomial.X^4 + Polynomial.C (373/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-907/70 : ℚ)*Polynomial.X^6 + Polynomial.C (194/35 : ℚ)*Polynomial.X^7 + Polynomial.C (9/14 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf1585.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1585.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1585.rational a+Real.sqrt 2*evalQPoly rf1585.irrational a)/evalQPoly rf1585.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1585,rf1528]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (6/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/70 : ℚ)*Polynomial.X^3 + Polynomial.C (4/7 : ℚ)*Polynomial.X^4 + Polynomial.C (169/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-162/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf1614.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1614.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1614.rational a+Real.sqrt 2*evalQPoly rf1614.irrational a)/evalQPoly rf1614.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1614,rf1528]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (6/5 : ℚ)*Polynomial.X^3 + Polynomial.C (-353/70 : ℚ)*Polynomial.X^4 + Polynomial.C (86/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-96/5 : ℚ)*Polynomial.X^6 + Polynomial.C (74/7 : ℚ)*Polynomial.X^7 + Polynomial.C (109/28 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1599.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1599.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1599.rational a+Real.sqrt 2*evalQPoly rf1599.irrational a)/evalQPoly rf1599.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1599,rf1528]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/70 : ℚ)*Polynomial.X^1 + Polynomial.C (69/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/10 : ℚ)*Polynomial.X^3 + Polynomial.C (379/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-419/70 : ℚ)*Polynomial.X^5 + Polynomial.C (111/70 : ℚ)*Polynomial.X^6 + Polynomial.C (15/14 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf1628.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1628.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1628.rational a+Real.sqrt 2*evalQPoly rf1628.irrational a)/evalQPoly rf1628.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1628,rf1528]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^1 + Polynomial.C (47/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-26/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/70 : ℚ)*Polynomial.X^4 + Polynomial.C (158/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-327/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-2 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1642.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1642.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1642.rational a+Real.sqrt 2*evalQPoly rf1642.irrational a)/evalQPoly rf1642.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1642,rf1528]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd029
