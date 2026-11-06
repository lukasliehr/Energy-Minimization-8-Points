import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd048
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1932.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (17/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-69/7 : ℚ)*Polynomial.X^2 + Polynomial.C (204/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-227/7 : ℚ)*Polynomial.X^4 + Polynomial.C (31/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-151/7 : ℚ)*Polynomial.X^6 + Polynomial.C (576/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-39 : ℚ)*Polynomial.X^8 + Polynomial.C (-65/2 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1932.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1932.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1932.rational a+Real.sqrt 2*evalQPoly rf1932.irrational a)/evalQPoly rf1932.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1932,rf1932]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (-95/28 : ℚ)*Polynomial.X^1 + Polynomial.C (221/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-261/28 : ℚ)*Polynomial.X^3 + Polynomial.C (575/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-1537/28 : ℚ)*Polynomial.X^5 + Polynomial.C (1675/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-123/28 : ℚ)*Polynomial.X^7 + Polynomial.C (-67/4 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1951.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1951.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1951.rational a+Real.sqrt 2*evalQPoly rf1951.irrational a)/evalQPoly rf1951.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1951,rf1932]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^1 + Polynomial.C (11/2 : ℚ)*Polynomial.X^2 + Polynomial.C (15/2 : ℚ)*Polynomial.X^3 + Polynomial.C (-49/2 : ℚ)*Polynomial.X^4 + Polynomial.C (31/2 : ℚ)*Polynomial.X^5 + Polynomial.C (5/2 : ℚ)*Polynomial.X^6 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1988.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1988.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1988.rational a+Real.sqrt 2*evalQPoly rf1988.irrational a)/evalQPoly rf1988.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1988,rf1932]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-3/14 : ℚ)*Polynomial.X^0 + Polynomial.C (11/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-60/7 : ℚ)*Polynomial.X^2 + Polynomial.C (218/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-348/7 : ℚ)*Polynomial.X^4 + Polynomial.C (83/7 : ℚ)*Polynomial.X^5 + Polynomial.C (2/7 : ℚ)*Polynomial.X^6 + Polynomial.C (760/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-263/2 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1969.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1969.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1969.rational a+Real.sqrt 2*evalQPoly rf1969.irrational a)/evalQPoly rf1969.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1969,rf1932]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2 : ℚ)*Polynomial.X^1 + Polynomial.C (67/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-101/7 : ℚ)*Polynomial.X^3 + Polynomial.C (18 : ℚ)*Polynomial.X^4 + Polynomial.C (-424/7 : ℚ)*Polynomial.X^5 + Polynomial.C (815/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-67 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf2006.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2006.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2006.rational a+Real.sqrt 2*evalQPoly rf2006.irrational a)/evalQPoly rf2006.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2006,rf1932]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/2 : ℚ)*Polynomial.X^1 + Polynomial.C (41/4 : ℚ)*Polynomial.X^2 + Polynomial.C (7 : ℚ)*Polynomial.X^3 + Polynomial.C (-155/4 : ℚ)*Polynomial.X^4 + Polynomial.C (77/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-49/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf2043.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2043.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2043.rational a+Real.sqrt 2*evalQPoly rf2043.irrational a)/evalQPoly rf2043.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2043,rf1932]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (145/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-417/14 : ℚ)*Polynomial.X^3 + Polynomial.C (411/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-555/14 : ℚ)*Polynomial.X^5 + Polynomial.C (1147/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-141/2 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf2024.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2024.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2024.rational a+Real.sqrt 2*evalQPoly rf2024.irrational a)/evalQPoly rf2024.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2024,rf1932]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1 : ℚ)*Polynomial.X^0 + Polynomial.C (67/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-101/14 : ℚ)*Polynomial.X^2 + Polynomial.C (9 : ℚ)*Polynomial.X^3 + Polynomial.C (-212/7 : ℚ)*Polynomial.X^4 + Polynomial.C (815/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-67/2 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf2061.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2061.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2061.rational a+Real.sqrt 2*evalQPoly rf2061.irrational a)/evalQPoly rf2061.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2061,rf1932]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (13/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^4 + Polynomial.C (47/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-1 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf2079.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2079.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2079.rational a+Real.sqrt 2*evalQPoly rf2079.irrational a)/evalQPoly rf2079.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2079,rf1932]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd048
