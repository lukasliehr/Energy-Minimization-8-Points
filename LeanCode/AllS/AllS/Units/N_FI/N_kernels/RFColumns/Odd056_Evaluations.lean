import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd056
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1940.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (25/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-59/14 : ℚ)*Polynomial.X^3 + Polynomial.C (235/28 : ℚ)*Polynomial.X^4 + Polynomial.C (0 : ℚ)*Polynomial.X^5 + Polynomial.C (-941/28 : ℚ)*Polynomial.X^6 + Polynomial.C (825/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-559/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-289/14 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1940.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1940.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1940.rational a+Real.sqrt 2*evalQPoly rf1940.irrational a)/evalQPoly rf1940.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1940,rf1940]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (5/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^2 + Polynomial.C (9/7 : ℚ)*Polynomial.X^3 + Polynomial.C (11/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-123/14 : ℚ)*Polynomial.X^5 + Polynomial.C (33/4 : ℚ)*Polynomial.X^6 + Polynomial.C (-8/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-18/7 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1959.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1959.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1959.rational a+Real.sqrt 2*evalQPoly rf1959.irrational a)/evalQPoly rf1959.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1959,rf1940]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (5/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^2 + Polynomial.C (8/7 : ℚ)*Polynomial.X^3 + Polynomial.C (101/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-123/14 : ℚ)*Polynomial.X^5 + Polynomial.C (87/28 : ℚ)*Polynomial.X^6 + Polynomial.C (3 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1996.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1996.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1996.rational a+Real.sqrt 2*evalQPoly rf1996.irrational a)/evalQPoly rf1996.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1996,rf1940]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (25/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-5 : ℚ)*Polynomial.X^3 + Polynomial.C (391/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-149/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-1013/28 : ℚ)*Polynomial.X^6 + Polynomial.C (688/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-2067/28 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1977.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1977.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1977.rational a+Real.sqrt 2*evalQPoly rf1977.irrational a)/evalQPoly rf1977.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1977,rf1940]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^2 + Polynomial.C (5/2 : ℚ)*Polynomial.X^3 + Polynomial.C (-2 : ℚ)*Polynomial.X^4 + Polynomial.C (-101/14 : ℚ)*Polynomial.X^5 + Polynomial.C (111/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-151/14 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf2014.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2014.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2014.rational a+Real.sqrt 2*evalQPoly rf2014.irrational a)/evalQPoly rf2014.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2014,rf1940]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-59/28 : ℚ)*Polynomial.X^2 + Polynomial.C (17/7 : ℚ)*Polynomial.X^3 + Polynomial.C (117/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-197/14 : ℚ)*Polynomial.X^5 + Polynomial.C (41/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf2051.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2051.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2051.rational a+Real.sqrt 2*evalQPoly rf2051.irrational a)/evalQPoly rf2051.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2051,rf1940]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-17/28 : ℚ)*Polynomial.X^2 + Polynomial.C (57/14 : ℚ)*Polynomial.X^3 + Polynomial.C (-141/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-74/7 : ℚ)*Polynomial.X^5 + Polynomial.C (99/4 : ℚ)*Polynomial.X^6 + Polynomial.C (-95/14 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf2032.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2032.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2032.rational a+Real.sqrt 2*evalQPoly rf2032.irrational a)/evalQPoly rf2032.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2032,rf1940]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/14 : ℚ)*Polynomial.X^1 + Polynomial.C (53/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-25/4 : ℚ)*Polynomial.X^4 + Polynomial.C (23/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-193/28 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf2069.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2069.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2069.rational a+Real.sqrt 2*evalQPoly rf2069.irrational a)/evalQPoly rf2069.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2069,rf1940]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (3/28 : ℚ)*Polynomial.X^2 + Polynomial.C (15/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-149/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-9/2 : ℚ)*Polynomial.X^5 + Polynomial.C (63/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf2085.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2085.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2085.rational a+Real.sqrt 2*evalQPoly rf2085.irrational a)/evalQPoly rf2085.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2085,rf1940]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd056
