import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd043
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1927.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (41/280 : ℚ)*Polynomial.X^1 + Polynomial.C (-221/140 : ℚ)*Polynomial.X^2 + Polynomial.C (691/140 : ℚ)*Polynomial.X^3 + Polynomial.C (387/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-264/5 : ℚ)*Polynomial.X^5 + Polynomial.C (2719/20 : ℚ)*Polynomial.X^6 + Polynomial.C (-22779/140 : ℚ)*Polynomial.X^7 + Polynomial.C (11337/140 : ℚ)*Polynomial.X^8 + Polynomial.C (5927/280 : ℚ)*Polynomial.X^9 + Polynomial.C (-754/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1927.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1927.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1927.rational a+Real.sqrt 2*evalQPoly rf1927.irrational a)/evalQPoly rf1927.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1927,rf1927]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (17/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-159/280 : ℚ)*Polynomial.X^1 + Polynomial.C (23/20 : ℚ)*Polynomial.X^2 + Polynomial.C (559/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-852/35 : ℚ)*Polynomial.X^4 + Polynomial.C (3889/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-9853/140 : ℚ)*Polynomial.X^6 + Polynomial.C (6229/140 : ℚ)*Polynomial.X^7 + Polynomial.C (1/40 : ℚ)*Polynomial.X^8 + Polynomial.C (-3821/280 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1946.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1946.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1946.rational a+Real.sqrt 2*evalQPoly rf1946.irrational a)/evalQPoly rf1946.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1946,rf1927]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (17/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-87/140 : ℚ)*Polynomial.X^1 + Polynomial.C (237/140 : ℚ)*Polynomial.X^2 + Polynomial.C (89/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-479/70 : ℚ)*Polynomial.X^4 + Polynomial.C (101/20 : ℚ)*Polynomial.X^5 + Polynomial.C (37/20 : ℚ)*Polynomial.X^6 + Polynomial.C (-19/20 : ℚ)*Polynomial.X^7 + Polynomial.C (-7/8 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1983.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1983.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1983.rational a+Real.sqrt 2*evalQPoly rf1983.irrational a)/evalQPoly rf1983.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1983,rf1927]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (73/280 : ℚ)*Polynomial.X^1 + Polynomial.C (-201/140 : ℚ)*Polynomial.X^2 + Polynomial.C (821/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-443/14 : ℚ)*Polynomial.X^5 + Polynomial.C (21649/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-38181/140 : ℚ)*Polynomial.X^7 + Polynomial.C (69679/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-24653/280 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1964.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1964.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1964.rational a+Real.sqrt 2*evalQPoly rf1964.irrational a)/evalQPoly rf1964.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1964,rf1927]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^1 + Polynomial.C (25/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-1189/70 : ℚ)*Polynomial.X^4 + Polynomial.C (885/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-7941/70 : ℚ)*Polynomial.X^6 + Polynomial.C (8063/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-3891/70 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2001.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2001.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2001.rational a+Real.sqrt 2*evalQPoly rf2001.irrational a)/evalQPoly rf2001.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2001,rf1927]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/10 : ℚ)*Polynomial.X^1 + Polynomial.C (92/35 : ℚ)*Polynomial.X^2 + Polynomial.C (3/14 : ℚ)*Polynomial.X^3 + Polynomial.C (-69/7 : ℚ)*Polynomial.X^4 + Polynomial.C (703/70 : ℚ)*Polynomial.X^5 + Polynomial.C (2/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2038.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2038.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2038.rational a+Real.sqrt 2*evalQPoly rf2038.irrational a)/evalQPoly rf2038.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2038,rf1927]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-17/280 : ℚ)*Polynomial.X^0 + Polynomial.C (1/4 : ℚ)*Polynomial.X^1 + Polynomial.C (183/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-669/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-803/70 : ℚ)*Polynomial.X^4 + Polynomial.C (9537/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-17767/140 : ℚ)*Polynomial.X^6 + Polynomial.C (16441/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-14339/280 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2019.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2019.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2019.rational a+Real.sqrt 2*evalQPoly rf2019.irrational a)/evalQPoly rf2019.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2019,rf1927]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-17/140 : ℚ)*Polynomial.X^0 + Polynomial.C (25/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-87/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-1189/140 : ℚ)*Polynomial.X^3 + Polynomial.C (885/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-7941/140 : ℚ)*Polynomial.X^5 + Polynomial.C (8063/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-3891/140 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2056.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2056.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2056.rational a+Real.sqrt 2*evalQPoly rf2056.irrational a)/evalQPoly rf2056.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2056,rf1927]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (33/140 : ℚ)*Polynomial.X^1 + Polynomial.C (11/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/20 : ℚ)*Polynomial.X^3 + Polynomial.C (3/4 : ℚ)*Polynomial.X^4 + Polynomial.C (459/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-163/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2074.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2074.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2074.rational a+Real.sqrt 2*evalQPoly rf2074.irrational a)/evalQPoly rf2074.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2074,rf1927]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd043
