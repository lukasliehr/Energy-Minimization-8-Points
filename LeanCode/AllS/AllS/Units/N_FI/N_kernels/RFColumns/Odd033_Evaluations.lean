import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd033
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1532.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (27/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/14 : ℚ)*Polynomial.X^3 + Polynomial.C (209/140 : ℚ)*Polynomial.X^4 + Polynomial.C (163/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-1391/140 : ℚ)*Polynomial.X^6 + Polynomial.C (67/14 : ℚ)*Polynomial.X^7 + Polynomial.C (199/28 : ℚ)*Polynomial.X^8 + Polynomial.C (48/35 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1532.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1532.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1532.rational a+Real.sqrt 2*evalQPoly rf1532.irrational a)/evalQPoly rf1532.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1532,rf1532]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/70 : ℚ)*Polynomial.X^2 + Polynomial.C (17/70 : ℚ)*Polynomial.X^3 + Polynomial.C (17/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^5 + Polynomial.C (47/70 : ℚ)*Polynomial.X^6 + Polynomial.C (43/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-9/140 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1547.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1547.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1547.rational a+Real.sqrt 2*evalQPoly rf1547.irrational a)/evalQPoly rf1547.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1547,rf1532]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-41/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^3 + Polynomial.C (213/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-4/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-251/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1575.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1575.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1575.rational a+Real.sqrt 2*evalQPoly rf1575.irrational a)/evalQPoly rf1575.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1575,rf1532]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (11/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/35 : ℚ)*Polynomial.X^3 + Polynomial.C (73/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-1551/140 : ℚ)*Polynomial.X^6 + Polynomial.C (106/7 : ℚ)*Polynomial.X^7 + Polynomial.C (663/140 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1561.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1561.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1561.rational a+Real.sqrt 2*evalQPoly rf1561.irrational a)/evalQPoly rf1561.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1561,rf1532]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (27/35 : ℚ)*Polynomial.X^3 + Polynomial.C (2/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-123/35 : ℚ)*Polynomial.X^5 + Polynomial.C (104/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-9/35 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1589.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1589.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1589.rational a+Real.sqrt 2*evalQPoly rf1589.irrational a)/evalQPoly rf1589.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1589,rf1532]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/140 : ℚ)*Polynomial.X^2 + Polynomial.C (9/35 : ℚ)*Polynomial.X^3 + Polynomial.C (197/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-12/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-7/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1618.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1618.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1618.rational a+Real.sqrt 2*evalQPoly rf1618.irrational a)/evalQPoly rf1618.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1618,rf1532]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-17/140 : ℚ)*Polynomial.X^2 + Polynomial.C (73/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-101/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-263/70 : ℚ)*Polynomial.X^5 + Polynomial.C (597/140 : ℚ)*Polynomial.X^6 + Polynomial.C (17/70 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1603.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1603.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1603.rational a+Real.sqrt 2*evalQPoly rf1603.irrational a)/evalQPoly rf1603.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1603,rf1532]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/70 : ℚ)*Polynomial.X^1 + Polynomial.C (18/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-29/14 : ℚ)*Polynomial.X^4 + Polynomial.C (171/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-22/35 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1632.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1632.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1632.rational a+Real.sqrt 2*evalQPoly rf1632.irrational a)/evalQPoly rf1632.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1632,rf1532]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (3/140 : ℚ)*Polynomial.X^2 + Polynomial.C (19/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/20 : ℚ)*Polynomial.X^4 + Polynomial.C (-13/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1645.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1645.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1645.rational a+Real.sqrt 2*evalQPoly rf1645.irrational a)/evalQPoly rf1645.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1645,rf1532]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd033
