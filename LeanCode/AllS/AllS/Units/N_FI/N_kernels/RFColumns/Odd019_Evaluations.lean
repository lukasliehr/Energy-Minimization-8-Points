import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd019
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1226.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (17/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-23/28 : ℚ)*Polynomial.X^3 + Polynomial.C (351/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-247/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-881/140 : ℚ)*Polynomial.X^6 + Polynomial.C (223/28 : ℚ)*Polynomial.X^7 + Polynomial.C (109/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1226.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1226.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1226.rational a+Real.sqrt 2*evalQPoly rf1226.irrational a)/evalQPoly rf1226.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1226,rf1226]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^2 + Polynomial.C (67/70 : ℚ)*Polynomial.X^3 + Polynomial.C (3/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-159/70 : ℚ)*Polynomial.X^5 + Polynomial.C (23/14 : ℚ)*Polynomial.X^6 + Polynomial.C (3/10 : ℚ)*Polynomial.X^7 + Polynomial.C (-43/140 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1237.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1237.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1237.rational a+Real.sqrt 2*evalQPoly rf1237.irrational a)/evalQPoly rf1237.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1237,rf1226]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-51/140 : ℚ)*Polynomial.X^2 + Polynomial.C (19/140 : ℚ)*Polynomial.X^3 + Polynomial.C (233/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-221/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-213/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1257.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1257.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1257.rational a+Real.sqrt 2*evalQPoly rf1257.irrational a)/evalQPoly rf1257.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1257,rf1226]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^3 + Polynomial.C (143/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-563/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-143/70 : ℚ)*Polynomial.X^6 + Polynomial.C (227/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-99/140 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1246.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1246.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1246.rational a+Real.sqrt 2*evalQPoly rf1246.irrational a)/evalQPoly rf1246.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1246,rf1226]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-12/35 : ℚ)*Polynomial.X^2 + Polynomial.C (47/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-52/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-69/35 : ℚ)*Polynomial.X^5 + Polynomial.C (128/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-43/35 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1266.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1266.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1266.rational a+Real.sqrt 2*evalQPoly rf1266.irrational a)/evalQPoly rf1266.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1266,rf1226]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^2 + Polynomial.C (2/5 : ℚ)*Polynomial.X^3 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-2 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1285.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1285.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1285.rational a+Real.sqrt 2*evalQPoly rf1285.irrational a)/evalQPoly rf1285.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1285,rf1226]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/140 : ℚ)*Polynomial.X^2 + Polynomial.C (269/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-361/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-491/140 : ℚ)*Polynomial.X^5 + Polynomial.C (877/140 : ℚ)*Polynomial.X^6 + Polynomial.C (3/140 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1276.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1276.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1276.rational a+Real.sqrt 2*evalQPoly rf1276.irrational a)/evalQPoly rf1276.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1276,rf1226]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^1 + Polynomial.C (9/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-18/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/70 : ℚ)*Polynomial.X^4 + Polynomial.C (32/35 : ℚ)*Polynomial.X^5 + Polynomial.C (27/70 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1295.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1295.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1295.rational a+Real.sqrt 2*evalQPoly rf1295.irrational a)/evalQPoly rf1295.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1295,rf1226]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (3/10 : ℚ)*Polynomial.X^2 + Polynomial.C (24/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-121/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-51/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1/2 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1305.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1305.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1305.rational a+Real.sqrt 2*evalQPoly rf1305.irrational a)/evalQPoly rf1305.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1305,rf1226]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd019
