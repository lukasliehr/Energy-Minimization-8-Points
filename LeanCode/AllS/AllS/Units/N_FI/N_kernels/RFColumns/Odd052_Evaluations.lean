import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd052
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1936.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (11/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-197/140 : ℚ)*Polynomial.X^3 + Polynomial.C (45/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-1047/70 : ℚ)*Polynomial.X^5 + Polynomial.C (62/5 : ℚ)*Polynomial.X^6 + Polynomial.C (969/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-993/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-353/140 : ℚ)*Polynomial.X^9 + Polynomial.C (165/14 : ℚ)*Polynomial.X^10 + Polynomial.C (2563/140 : ℚ)*Polynomial.X^11 + Polynomial.C (44/7 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1936.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1936.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1936.rational a+Real.sqrt 2*evalQPoly rf1936.irrational a)/evalQPoly rf1936.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1936,rf1936]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (9/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-129/140 : ℚ)*Polynomial.X^2 + Polynomial.C (461/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-81/14 : ℚ)*Polynomial.X^4 + Polynomial.C (219/70 : ℚ)*Polynomial.X^5 + Polynomial.C (39/10 : ℚ)*Polynomial.X^6 + Polynomial.C (-30/7 : ℚ)*Polynomial.X^7 + Polynomial.C (3/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-96/35 : ℚ)*Polynomial.X^9 + Polynomial.C (263/140 : ℚ)*Polynomial.X^10 + Polynomial.C (39/28 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1955.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1955.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1955.rational a+Real.sqrt 2*evalQPoly rf1955.irrational a)/evalQPoly rf1955.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1955,rf1936]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (4/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-93/140 : ℚ)*Polynomial.X^2 + Polynomial.C (52/35 : ℚ)*Polynomial.X^3 + Polynomial.C (29/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-244/35 : ℚ)*Polynomial.X^5 + Polynomial.C (79/10 : ℚ)*Polynomial.X^6 + Polynomial.C (4 : ℚ)*Polynomial.X^7 + Polynomial.C (-761/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-32/5 : ℚ)*Polynomial.X^9 + Polynomial.C (-7/4 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1992.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1992.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1992.rational a+Real.sqrt 2*evalQPoly rf1992.irrational a)/evalQPoly rf1992.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1992,rf1936]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (17/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-107/140 : ℚ)*Polynomial.X^2 + Polynomial.C (251/140 : ℚ)*Polynomial.X^3 + Polynomial.C (23/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-1571/70 : ℚ)*Polynomial.X^5 + Polynomial.C (3231/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1557/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-5297/140 : ℚ)*Polynomial.X^8 + Polynomial.C (865/28 : ℚ)*Polynomial.X^9 + Polynomial.C (2269/140 : ℚ)*Polynomial.X^10 + Polynomial.C (627/28 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1973.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1973.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1973.rational a+Real.sqrt 2*evalQPoly rf1973.irrational a)/evalQPoly rf1973.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1973,rf1936]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^2 + Polynomial.C (99/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-292/35 : ℚ)*Polynomial.X^4 + Polynomial.C (381/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-32/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-383/35 : ℚ)*Polynomial.X^7 + Polynomial.C (212/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-26/7 : ℚ)*Polynomial.X^9 + Polynomial.C (32/7 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf2010.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2010.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2010.rational a+Real.sqrt 2*evalQPoly rf2010.irrational a)/evalQPoly rf2010.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2010,rf1936]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (13/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/14 : ℚ)*Polynomial.X^4 + Polynomial.C (221/70 : ℚ)*Polynomial.X^5 + Polynomial.C (51/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-194/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-23/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf2047.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2047.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2047.rational a+Real.sqrt 2*evalQPoly rf2047.irrational a)/evalQPoly rf2047.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2047,rf1936]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (29/140 : ℚ)*Polynomial.X^2 + Polynomial.C (47/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-613/70 : ℚ)*Polynomial.X^4 + Polynomial.C (125/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-617/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-523/35 : ℚ)*Polynomial.X^7 + Polynomial.C (1609/140 : ℚ)*Polynomial.X^8 + Polynomial.C (94/35 : ℚ)*Polynomial.X^9 + Polynomial.C (177/28 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf2028.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2028.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2028.rational a+Real.sqrt 2*evalQPoly rf2028.irrational a)/evalQPoly rf2028.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2028,rf1936]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (7/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-281/70 : ℚ)*Polynomial.X^3 + Polynomial.C (169/35 : ℚ)*Polynomial.X^4 + Polynomial.C (9/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-199/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-111/70 : ℚ)*Polynomial.X^7 + Polynomial.C (409/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-17/14 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf2065.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2065.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2065.rational a+Real.sqrt 2*evalQPoly rf2065.irrational a)/evalQPoly rf2065.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2065,rf1936]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (13/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/14 : ℚ)*Polynomial.X^4 + Polynomial.C (221/70 : ℚ)*Polynomial.X^5 + Polynomial.C (51/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-194/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-23/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf2047.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2047.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2047.rational a+Real.sqrt 2*evalQPoly rf2047.irrational a)/evalQPoly rf2047.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2047,rf1936]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd052
