import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd058
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1942.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/2 : ℚ)*Polynomial.X^3 + Polynomial.C (40 : ℚ)*Polynomial.X^4 + Polynomial.C (-50 : ℚ)*Polynomial.X^5 + Polynomial.C (37/2 : ℚ)*Polynomial.X^6 + Polynomial.C (39/2 : ℚ)*Polynomial.X^7
theorem eval0 (a : ℝ) (h : rf1942.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1942.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1942.rational a+Real.sqrt 2*evalQPoly rf1942.irrational a)/evalQPoly rf1942.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1942,rf1942]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/4 : ℚ)*Polynomial.X^1 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^2 + Polynomial.C (7 : ℚ)*Polynomial.X^3 + Polynomial.C (-6 : ℚ)*Polynomial.X^4 + Polynomial.C (1/4 : ℚ)*Polynomial.X^5 + Polynomial.C (7/4 : ℚ)*Polynomial.X^6
theorem eval1 (a : ℝ) (h : rf1961.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1961.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1961.rational a+Real.sqrt 2*evalQPoly rf1961.irrational a)/evalQPoly rf1961.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1961,rf1942]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-4 : ℚ)*Polynomial.X^2 + Polynomial.C (6 : ℚ)*Polynomial.X^3 + Polynomial.C (-4 : ℚ)*Polynomial.X^4 + Polynomial.C (-3 : ℚ)*Polynomial.X^5
theorem eval2 (a : ℝ) (h : rf1998.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1998.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1998.rational a+Real.sqrt 2*evalQPoly rf1998.irrational a)/evalQPoly rf1998.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1998,rf1942]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3 : ℚ)*Polynomial.X^2 + Polynomial.C (-20 : ℚ)*Polynomial.X^3 + Polynomial.C (64 : ℚ)*Polynomial.X^4 + Polynomial.C (-92 : ℚ)*Polynomial.X^5 + Polynomial.C (69 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1979.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1979.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1979.rational a+Real.sqrt 2*evalQPoly rf1979.irrational a)/evalQPoly rf1979.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1979,rf1942]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (9 : ℚ)*Polynomial.X^3 + Polynomial.C (-13 : ℚ)*Polynomial.X^4 + Polynomial.C (7 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf2016.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2016.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2016.rational a+Real.sqrt 2*evalQPoly rf2016.irrational a)/evalQPoly rf2016.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2016,rf1942]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/4 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/2 : ℚ)*Polynomial.X^2 + Polynomial.C (11 : ℚ)*Polynomial.X^3 + Polynomial.C (-41/4 : ℚ)*Polynomial.X^4
theorem eval5 (a : ℝ) (h : rf2053.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2053.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2053.rational a+Real.sqrt 2*evalQPoly rf2053.irrational a)/evalQPoly rf2053.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2053,rf1942]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (9 : ℚ)*Polynomial.X^3 + Polynomial.C (-9 : ℚ)*Polynomial.X^4 + Polynomial.C (3 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf2034.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2034.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2034.rational a+Real.sqrt 2*evalQPoly rf2034.irrational a)/evalQPoly rf2034.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2034,rf1942]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^1 + Polynomial.C (9/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/2 : ℚ)*Polynomial.X^3 + Polynomial.C (7/2 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf2071.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2071.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2071.rational a+Real.sqrt 2*evalQPoly rf2071.irrational a)/evalQPoly rf2071.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2071,rf1942]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-6 : ℚ)*Polynomial.X^2 + Polynomial.C (16 : ℚ)*Polynomial.X^3 + Polynomial.C (-18 : ℚ)*Polynomial.X^4
theorem eval8 (a : ℝ) (h : rf1487.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1487.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1487.rational a+Real.sqrt 2*evalQPoly rf1487.irrational a)/evalQPoly rf1487.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1487,rf1942]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd058
