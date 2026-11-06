import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd054
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1938.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (5/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-55/28 : ℚ)*Polynomial.X^2 + Polynomial.C (227/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-347/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-263/28 : ℚ)*Polynomial.X^5 + Polynomial.C (1487/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-1499/28 : ℚ)*Polynomial.X^7 + Polynomial.C (21/4 : ℚ)*Polynomial.X^8 + Polynomial.C (213/14 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1938.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1938.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1938.rational a+Real.sqrt 2*evalQPoly rf1938.irrational a)/evalQPoly rf1938.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1938,rf1938]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^1 + Polynomial.C (17/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-2 : ℚ)*Polynomial.X^3 + Polynomial.C (-39/7 : ℚ)*Polynomial.X^4 + Polynomial.C (11 : ℚ)*Polynomial.X^5 + Polynomial.C (-3 : ℚ)*Polynomial.X^6 + Polynomial.C (-18/7 : ℚ)*Polynomial.X^7 + Polynomial.C (5/14 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1957.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1957.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1957.rational a+Real.sqrt 2*evalQPoly rf1957.irrational a)/evalQPoly rf1957.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1957,rf1938]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/14 : ℚ)*Polynomial.X^1 + Polynomial.C (37/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/14 : ℚ)*Polynomial.X^3 + Polynomial.C (-129/14 : ℚ)*Polynomial.X^4 + Polynomial.C (187/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^6 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1994.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1994.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1994.rational a+Real.sqrt 2*evalQPoly rf1994.irrational a)/evalQPoly rf1994.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1994,rf1938]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (9/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-25/14 : ℚ)*Polynomial.X^2 + Polynomial.C (227/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-145/7 : ℚ)*Polynomial.X^4 + Polynomial.C (267/28 : ℚ)*Polynomial.X^5 + Polynomial.C (907/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-3159/28 : ℚ)*Polynomial.X^7 + Polynomial.C (1473/28 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1975.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1975.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1975.rational a+Real.sqrt 2*evalQPoly rf1975.irrational a)/evalQPoly rf1975.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1975,rf1938]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (16/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^4 + Polynomial.C (110/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-92/7 : ℚ)*Polynomial.X^6 + Polynomial.C (10/7 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf2012.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2012.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2012.rational a+Real.sqrt 2*evalQPoly rf2012.irrational a)/evalQPoly rf2012.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2012,rf1938]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/7 : ℚ)*Polynomial.X^1 + Polynomial.C (4 : ℚ)*Polynomial.X^2 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-81/7 : ℚ)*Polynomial.X^4 + Polynomial.C (165/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-12 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf2049.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2049.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2049.rational a+Real.sqrt 2*evalQPoly rf2049.irrational a)/evalQPoly rf2049.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2049,rf1938]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (10/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-123/14 : ℚ)*Polynomial.X^3 + Polynomial.C (117/14 : ℚ)*Polynomial.X^4 + Polynomial.C (142/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-232/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-29/14 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf2030.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2030.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2030.rational a+Real.sqrt 2*evalQPoly rf2030.irrational a)/evalQPoly rf2030.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2030,rf1938]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/7 : ℚ)*Polynomial.X^0 + Polynomial.C (8/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (55/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-46/7 : ℚ)*Polynomial.X^5 + Polynomial.C (5/7 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf2067.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2067.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2067.rational a+Real.sqrt 2*evalQPoly rf2067.irrational a)/evalQPoly rf2067.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2067,rf1938]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^3 + Polynomial.C (19/4 : ℚ)*Polynomial.X^4 + Polynomial.C (23/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-59/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf2083.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2083.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2083.rational a+Real.sqrt 2*evalQPoly rf2083.irrational a)/evalQPoly rf2083.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2083,rf1938]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd054
