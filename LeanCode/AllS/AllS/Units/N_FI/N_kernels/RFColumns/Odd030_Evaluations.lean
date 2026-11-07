import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd030
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1529.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/28 : ℚ)*Polynomial.X^2 + Polynomial.C (27/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-373/140 : ℚ)*Polynomial.X^5 + Polynomial.C (87/140 : ℚ)*Polynomial.X^6 + Polynomial.C (1459/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-937/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-156/35 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1529.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1529.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1529.rational a+Real.sqrt 2*evalQPoly rf1529.irrational a)/evalQPoly rf1529.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1529,rf1529]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/140 : ℚ)*Polynomial.X^1 + Polynomial.C (47/140 : ℚ)*Polynomial.X^2 + Polynomial.C (9/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-53/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-373/140 : ℚ)*Polynomial.X^5 + Polynomial.C (809/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-39/20 : ℚ)*Polynomial.X^7 + Polynomial.C (-277/140 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1544.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1544.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1544.rational a+Real.sqrt 2*evalQPoly rf1544.irrational a)/evalQPoly rf1544.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1544,rf1529]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (12/35 : ℚ)*Polynomial.X^2 + Polynomial.C (29/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-25/14 : ℚ)*Polynomial.X^4 + Polynomial.C (1/35 : ℚ)*Polynomial.X^5 + Polynomial.C (54/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1/2 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf0431.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0431.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0431.rational a+Real.sqrt 2*evalQPoly rf0431.irrational a)/evalQPoly rf0431.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0431,rf1529]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/70 : ℚ)*Polynomial.X^2 + Polynomial.C (209/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-157/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-75/28 : ℚ)*Polynomial.X^5 + Polynomial.C (481/70 : ℚ)*Polynomial.X^6 + Polynomial.C (1387/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-2461/140 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1558.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1558.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1558.rational a+Real.sqrt 2*evalQPoly rf1558.irrational a)/evalQPoly rf1558.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1558,rf1529]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (31/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-23/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-19/35 : ℚ)*Polynomial.X^5 + Polynomial.C (99/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-519/70 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1586.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1586.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1586.rational a+Real.sqrt 2*evalQPoly rf1586.irrational a)/evalQPoly rf1586.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1586,rf1529]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^1 + Polynomial.C (109/140 : ℚ)*Polynomial.X^2 + Polynomial.C (2/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-463/140 : ℚ)*Polynomial.X^4 + Polynomial.C (33/14 : ℚ)*Polynomial.X^5 + Polynomial.C (5/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1615.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1615.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1615.rational a+Real.sqrt 2*evalQPoly rf1615.irrational a)/evalQPoly rf1615.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1615,rf1529]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-54/35 : ℚ)*Polynomial.X^3 + Polynomial.C (1/10 : ℚ)*Polynomial.X^4 + Polynomial.C (53/35 : ℚ)*Polynomial.X^5 + Polynomial.C (457/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-277/35 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1600.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1600.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1600.rational a+Real.sqrt 2*evalQPoly rf1600.irrational a)/evalQPoly rf1600.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1600,rf1529]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/7 : ℚ)*Polynomial.X^4 + Polynomial.C (281/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-277/70 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1629.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1629.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1629.rational a+Real.sqrt 2*evalQPoly rf1629.irrational a)/evalQPoly rf1629.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1629,rf1529]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (9/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-18/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/140 : ℚ)*Polynomial.X^4 + Polynomial.C (89/70 : ℚ)*Polynomial.X^5 + Polynomial.C (1/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1643.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1643.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1643.rational a+Real.sqrt 2*evalQPoly rf1643.irrational a)/evalQPoly rf1643.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1643,rf1529]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd030
