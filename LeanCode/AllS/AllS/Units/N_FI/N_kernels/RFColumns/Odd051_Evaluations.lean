import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd051
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1935.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (33/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-108/7 : ℚ)*Polynomial.X^3 + Polynomial.C (72/7 : ℚ)*Polynomial.X^4 + Polynomial.C (390/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-965/7 : ℚ)*Polynomial.X^6 + Polynomial.C (740/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^8 + Polynomial.C (-421/14 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1935.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1935.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1935.rational a+Real.sqrt 2*evalQPoly rf1935.irrational a)/evalQPoly rf1935.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1935,rf1935]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-3/14 : ℚ)*Polynomial.X^0 + Polynomial.C (12/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-117/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/14 : ℚ)*Polynomial.X^3 + Polynomial.C (611/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-285/7 : ℚ)*Polynomial.X^5 + Polynomial.C (865/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-41/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-281/28 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1954.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1954.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1954.rational a+Real.sqrt 2*evalQPoly rf1954.irrational a)/evalQPoly rf1954.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1954,rf1935]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-3/14 : ℚ)*Polynomial.X^0 + Polynomial.C (25/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-57/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-25/14 : ℚ)*Polynomial.X^3 + Polynomial.C (227/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-209/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^6 + Polynomial.C (7/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1991.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1991.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1991.rational a+Real.sqrt 2*evalQPoly rf1991.irrational a)/evalQPoly rf1991.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1991,rf1935]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/14 : ℚ)*Polynomial.X^1 + Polynomial.C (57/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-237/14 : ℚ)*Polynomial.X^3 + Polynomial.C (415/14 : ℚ)*Polynomial.X^4 + Polynomial.C (345/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-2473/14 : ℚ)*Polynomial.X^6 + Polynomial.C (3373/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-800/7 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1972.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1972.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1972.rational a+Real.sqrt 2*evalQPoly rf1972.irrational a)/evalQPoly rf1972.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1972,rf1935]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (6/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-36/7 : ℚ)*Polynomial.X^2 + Polynomial.C (51/7 : ℚ)*Polynomial.X^3 + Polynomial.C (92/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-376/7 : ℚ)*Polynomial.X^5 + Polynomial.C (480/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-281/7 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf2009.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2009.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2009.rational a+Real.sqrt 2*evalQPoly rf2009.irrational a)/evalQPoly rf2009.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2009,rf1935]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-2/7 : ℚ)*Polynomial.X^0 + Polynomial.C (18/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-48/7 : ℚ)*Polynomial.X^2 + Polynomial.C (4/7 : ℚ)*Polynomial.X^3 + Polynomial.C (158/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-214/7 : ℚ)*Polynomial.X^5 + Polynomial.C (12 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf2046.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2046.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2046.rational a+Real.sqrt 2*evalQPoly rf2046.irrational a)/evalQPoly rf2046.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2046,rf1935]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (3/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-61/14 : ℚ)*Polynomial.X^2 + Polynomial.C (31/2 : ℚ)*Polynomial.X^3 + Polynomial.C (13/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-897/14 : ℚ)*Polynomial.X^5 + Polynomial.C (1373/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-513/14 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf2027.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2027.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2027.rational a+Real.sqrt 2*evalQPoly rf2027.irrational a)/evalQPoly rf2027.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2027,rf1935]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (13/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-39/14 : ℚ)*Polynomial.X^1 + Polynomial.C (109/28 : ℚ)*Polynomial.X^2 + Polynomial.C (7 : ℚ)*Polynomial.X^3 + Polynomial.C (-785/28 : ℚ)*Polynomial.X^4 + Polynomial.C (493/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-569/28 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf2064.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2064.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2064.rational a+Real.sqrt 2*evalQPoly rf2064.irrational a)/evalQPoly rf2064.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2064,rf1935]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (4 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-15/7 : ℚ)*Polynomial.X^5 + Polynomial.C (10 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf2081.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2081.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2081.rational a+Real.sqrt 2*evalQPoly rf2081.irrational a)/evalQPoly rf2081.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2081,rf1935]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd051
