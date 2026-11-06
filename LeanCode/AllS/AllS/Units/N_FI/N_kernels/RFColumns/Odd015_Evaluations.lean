import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd015
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1222.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (93/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-382/7 : ℚ)*Polynomial.X^4 + Polynomial.C (431/7 : ℚ)*Polynomial.X^5 + Polynomial.C (2 : ℚ)*Polynomial.X^6 + Polynomial.C (-95/7 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf1222.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1222.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1222.rational a+Real.sqrt 2*evalQPoly rf1222.irrational a)/evalQPoly rf1222.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1222,rf1222]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (117/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-162/7 : ℚ)*Polynomial.X^3 + Polynomial.C (169/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-32/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-123/14 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf1233.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1233.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1233.rational a+Real.sqrt 2*evalQPoly rf1233.irrational a)/evalQPoly rf1233.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1233,rf1222]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-3/7 : ℚ)*Polynomial.X^0 + Polynomial.C (11/7 : ℚ)*Polynomial.X^1 + Polynomial.C (10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-34/7 : ℚ)*Polynomial.X^3 + Polynomial.C (9/7 : ℚ)*Polynomial.X^4 + Polynomial.C (1 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf1253.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1253.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1253.rational a+Real.sqrt 2*evalQPoly rf1253.irrational a)/evalQPoly rf1253.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1253,rf1222]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (18/7 : ℚ)*Polynomial.X^2 + Polynomial.C (20/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-369/7 : ℚ)*Polynomial.X^4 + Polynomial.C (113 : ℚ)*Polynomial.X^5 + Polynomial.C (-394/7 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1242.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1242.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1242.rational a+Real.sqrt 2*evalQPoly rf1242.irrational a)/evalQPoly rf1242.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1242,rf1222]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/7 : ℚ)*Polynomial.X^1 + Polynomial.C (20/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-178/7 : ℚ)*Polynomial.X^3 + Polynomial.C (324/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-239/7 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf1262.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1262.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1262.rational a+Real.sqrt 2*evalQPoly rf1262.irrational a)/evalQPoly rf1262.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1262,rf1222]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-4/7 : ℚ)*Polynomial.X^0 + Polynomial.C (16/7 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-48/7 : ℚ)*Polynomial.X^3 + Polynomial.C (4 : ℚ)*Polynomial.X^4
theorem eval5 (a : ℝ) (h : rf1281.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1281.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1281.rational a+Real.sqrt 2*evalQPoly rf1281.irrational a)/evalQPoly rf1281.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1281,rf1222]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (3/7 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-172/7 : ℚ)*Polynomial.X^3 + Polynomial.C (345/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-239/7 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1272.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1272.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1272.rational a+Real.sqrt 2*evalQPoly rf1272.irrational a)/evalQPoly rf1272.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1272,rf1222]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (9/14 : ℚ)*Polynomial.X^0 + Polynomial.C (10/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-89/7 : ℚ)*Polynomial.X^2 + Polynomial.C (162/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-239/14 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf1291.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1291.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1291.rational a+Real.sqrt 2*evalQPoly rf1291.irrational a)/evalQPoly rf1291.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1291,rf1222]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (-22/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-4 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf1301.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1301.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1301.rational a+Real.sqrt 2*evalQPoly rf1301.irrational a)/evalQPoly rf1301.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1301,rf1222]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd015
