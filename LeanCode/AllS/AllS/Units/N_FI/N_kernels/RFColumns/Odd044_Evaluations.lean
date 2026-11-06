import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd044
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1928.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/7 : ℚ)*Polynomial.X^1 + Polynomial.C (407/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-5155/28 : ℚ)*Polynomial.X^4 + Polynomial.C (8193/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-22767/28 : ℚ)*Polynomial.X^6 + Polynomial.C (3265/7 : ℚ)*Polynomial.X^7 + Polynomial.C (2523/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-239/2 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1928.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1928.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1928.rational a+Real.sqrt 2*evalQPoly rf1928.irrational a)/evalQPoly rf1928.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1928,rf1928]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-31/28 : ℚ)*Polynomial.X^0 + Polynomial.C (55/14 : ℚ)*Polynomial.X^1 + Polynomial.C (333/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-678/7 : ℚ)*Polynomial.X^3 + Polynomial.C (7109/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-4821/14 : ℚ)*Polynomial.X^5 + Polynomial.C (6059/28 : ℚ)*Polynomial.X^6 + Polynomial.C (45/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-137/2 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1947.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1947.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1947.rational a+Real.sqrt 2*evalQPoly rf1947.irrational a)/evalQPoly rf1947.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1947,rf1928]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-5/4 : ℚ)*Polynomial.X^0 + Polynomial.C (7 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/2 : ℚ)*Polynomial.X^3 + Polynomial.C (141/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-16 : ℚ)*Polynomial.X^5 + Polynomial.C (-17/4 : ℚ)*Polynomial.X^6 + Polynomial.C (7/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1984.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1984.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1984.rational a+Real.sqrt 2*evalQPoly rf1984.irrational a)/evalQPoly rf1984.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1984,rf1928]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/14 : ℚ)*Polynomial.X^1 + Polynomial.C (445/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-249/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-2389/28 : ℚ)*Polynomial.X^4 + Polynomial.C (8479/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-35381/28 : ℚ)*Polynomial.X^6 + Polynomial.C (9014/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-1943/4 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1965.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1965.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1965.rational a+Real.sqrt 2*evalQPoly rf1965.irrational a)/evalQPoly rf1965.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1965,rf1928]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-51/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-787/14 : ℚ)*Polynomial.X^3 + Polynomial.C (1870/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-7575/14 : ℚ)*Polynomial.X^5 + Polynomial.C (3989/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-547/2 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf2002.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2002.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2002.rational a+Real.sqrt 2*evalQPoly rf2002.irrational a)/evalQPoly rf2002.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2002,rf1928]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-7/4 : ℚ)*Polynomial.X^0 + Polynomial.C (21/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-49/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-21 : ℚ)*Polynomial.X^3 + Polynomial.C (231/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-91/2 : ℚ)*Polynomial.X^5 + Polynomial.C (49/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf2039.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2039.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2039.rational a+Real.sqrt 2*evalQPoly rf2039.irrational a)/evalQPoly rf2039.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2039,rf1928]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (5/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-225/7 : ℚ)*Polynomial.X^3 + Polynomial.C (1035/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-8137/14 : ℚ)*Polynomial.X^5 + Polynomial.C (16803/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-270 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf2020.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2020.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2020.rational a+Real.sqrt 2*evalQPoly rf2020.irrational a)/evalQPoly rf2020.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2020,rf1928]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (9/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-51/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-787/28 : ℚ)*Polynomial.X^2 + Polynomial.C (935/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-7575/28 : ℚ)*Polynomial.X^4 + Polynomial.C (3989/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-547/4 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf2057.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2057.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2057.rational a+Real.sqrt 2*evalQPoly rf2057.irrational a)/evalQPoly rf2057.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2057,rf1928]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (3/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-23/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-157/28 : ℚ)*Polynomial.X^2 + Polynomial.C (31/7 : ℚ)*Polynomial.X^3 + Polynomial.C (75/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-279/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-69/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf2075.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2075.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2075.rational a+Real.sqrt 2*evalQPoly rf2075.irrational a)/evalQPoly rf2075.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2075,rf1928]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd044
