import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even078
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1670.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/136 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/68 : ℚ)*Polynomial.X^2 + Polynomial.C (45/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-95/34 : ℚ)*Polynomial.X^4 + Polynomial.C (283/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-575/34 : ℚ)*Polynomial.X^6 + Polynomial.C (1467/68 : ℚ)*Polynomial.X^7 + Polynomial.C (-471/34 : ℚ)*Polynomial.X^8 + Polynomial.C (3/136 : ℚ)*Polynomial.X^9 + Polynomial.C (273/68 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1670.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1670.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1670.rational a+Real.sqrt 2*evalQPoly rf1670.irrational a)/evalQPoly rf1670.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1670,rf1670]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/68 : ℚ)*Polynomial.X^2 + Polynomial.C (21/68 : ℚ)*Polynomial.X^3 + Polynomial.C (77/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-579/68 : ℚ)*Polynomial.X^5 + Polynomial.C (1393/68 : ℚ)*Polynomial.X^6 + Polynomial.C (-1393/68 : ℚ)*Polynomial.X^7 + Polynomial.C (147/68 : ℚ)*Polynomial.X^8 + Polynomial.C (251/34 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1694.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1694.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1694.rational a+Real.sqrt 2*evalQPoly rf1694.irrational a)/evalQPoly rf1694.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1694,rf1670]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/68 : ℚ)*Polynomial.X^1 + Polynomial.C (1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-107/68 : ℚ)*Polynomial.X^3 + Polynomial.C (343/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-587/68 : ℚ)*Polynomial.X^5 + Polynomial.C (471/68 : ℚ)*Polynomial.X^6 + Polynomial.C (-49/68 : ℚ)*Polynomial.X^7 + Polynomial.C (-7/4 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1740.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1740.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1740.rational a+Real.sqrt 2*evalQPoly rf1740.irrational a)/evalQPoly rf1740.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1740,rf1670]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^5 + Polynomial.C (10/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-1 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1809.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1809.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1809.rational a+Real.sqrt 2*evalQPoly rf1809.irrational a)/evalQPoly rf1809.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1809,rf1670]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/136 : ℚ)*Polynomial.X^0 + Polynomial.C (15/136 : ℚ)*Polynomial.X^1 + Polynomial.C (-14/17 : ℚ)*Polynomial.X^2 + Polynomial.C (275/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-909/68 : ℚ)*Polynomial.X^4 + Polynomial.C (1023/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-793/17 : ℚ)*Polynomial.X^6 + Polynomial.C (3373/68 : ℚ)*Polynomial.X^7 + Polynomial.C (-4621/136 : ℚ)*Polynomial.X^8 + Polynomial.C (1621/136 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1716.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1716.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1716.rational a+Real.sqrt 2*evalQPoly rf1716.irrational a)/evalQPoly rf1716.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1716,rf1670]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (9/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/34 : ℚ)*Polynomial.X^2 + Polynomial.C (-35/68 : ℚ)*Polynomial.X^3 + Polynomial.C (122/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-1653/68 : ℚ)*Polynomial.X^5 + Polynomial.C (1503/34 : ℚ)*Polynomial.X^6 + Polynomial.C (-3049/68 : ℚ)*Polynomial.X^7 + Polynomial.C (1421/68 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1763.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1763.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1763.rational a+Real.sqrt 2*evalQPoly rf1763.irrational a)/evalQPoly rf1763.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1763,rf1670]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/34 : ℚ)*Polynomial.X^1 + Polynomial.C (127/68 : ℚ)*Polynomial.X^2 + Polynomial.C (-123/17 : ℚ)*Polynomial.X^3 + Polynomial.C (1123/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-751/34 : ℚ)*Polynomial.X^5 + Polynomial.C (1101/68 : ℚ)*Polynomial.X^6 + Polynomial.C (-5 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1831.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1831.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1831.rational a+Real.sqrt 2*evalQPoly rf1831.irrational a)/evalQPoly rf1831.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1831,rf1670]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/136 : ℚ)*Polynomial.X^0 + Polynomial.C (11/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-45/34 : ℚ)*Polynomial.X^2 + Polynomial.C (385/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-1011/68 : ℚ)*Polynomial.X^4 + Polynomial.C (1765/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-1057/34 : ℚ)*Polynomial.X^6 + Polynomial.C (1647/68 : ℚ)*Polynomial.X^7 + Polynomial.C (-1313/136 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1785.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1785.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1785.rational a+Real.sqrt 2*evalQPoly rf1785.irrational a)/evalQPoly rf1785.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1785,rf1670]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-21/34 : ℚ)*Polynomial.X^2 + Polynomial.C (71/34 : ℚ)*Polynomial.X^3 + Polynomial.C (-23/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-129/17 : ℚ)*Polynomial.X^5 + Polynomial.C (623/34 : ℚ)*Polynomial.X^6 + Polynomial.C (-451/34 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1854.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1854.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1854.rational a+Real.sqrt 2*evalQPoly rf1854.irrational a)/evalQPoly rf1854.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1854,rf1670]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/17 : ℚ)*Polynomial.X^1 + Polynomial.C (149/68 : ℚ)*Polynomial.X^2 + Polynomial.C (-134/17 : ℚ)*Polynomial.X^3 + Polynomial.C (1031/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-263/17 : ℚ)*Polynomial.X^5 + Polynomial.C (27/4 : ℚ)*Polynomial.X^6
theorem eval9 (a : ℝ) (h : rf1900.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1900.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1900.rational a+Real.sqrt 2*evalQPoly rf1900.irrational a)/evalQPoly rf1900.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1900,rf1670]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (5/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-21/34 : ℚ)*Polynomial.X^2 + Polynomial.C (115/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-15/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-317/68 : ℚ)*Polynomial.X^5 + Polynomial.C (331/34 : ℚ)*Polynomial.X^6 + Polynomial.C (-427/68 : ℚ)*Polynomial.X^7
theorem eval10 (a : ℝ) (h : rf1876.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1876.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1876.rational a+Real.sqrt 2*evalQPoly rf1876.irrational a)/evalQPoly rf1876.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1876,rf1670]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^2 + Polynomial.C (88/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-1097/68 : ℚ)*Polynomial.X^4 + Polynomial.C (414/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-1021/68 : ℚ)*Polynomial.X^6
theorem eval11 (a : ℝ) (h : rf1923.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1923.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1923.rational a+Real.sqrt 2*evalQPoly rf1923.irrational a)/evalQPoly rf1923.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1923,rf1670]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even078
