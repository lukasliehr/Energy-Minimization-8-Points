import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd032
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1531.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (41/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-38/5 : ℚ)*Polynomial.X^4 + Polynomial.C (842/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-241/7 : ℚ)*Polynomial.X^6 + Polynomial.C (136/35 : ℚ)*Polynomial.X^7 + Polynomial.C (1346/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-314/35 : ℚ)*Polynomial.X^9 + Polynomial.C (-2081/70 : ℚ)*Polynomial.X^10 + Polynomial.C (-61/7 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1531.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1531.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1531.rational a+Real.sqrt 2*evalQPoly rf1531.irrational a)/evalQPoly rf1531.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1531,rf1531]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-164/35 : ℚ)*Polynomial.X^3 + Polynomial.C (51/5 : ℚ)*Polynomial.X^4 + Polynomial.C (-349/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-37/70 : ℚ)*Polynomial.X^6 + Polynomial.C (202/35 : ℚ)*Polynomial.X^7 + Polynomial.C (339/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^9 + Polynomial.C (-19/14 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1546.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1546.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1546.rational a+Real.sqrt 2*evalQPoly rf1546.irrational a)/evalQPoly rf1546.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1546,rf1531]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/140 : ℚ)*Polynomial.X^1 + Polynomial.C (27/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-72/35 : ℚ)*Polynomial.X^3 + Polynomial.C (9/14 : ℚ)*Polynomial.X^4 + Polynomial.C (113/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-491/35 : ℚ)*Polynomial.X^6 + Polynomial.C (0 : ℚ)*Polynomial.X^7 + Polynomial.C (1509/140 : ℚ)*Polynomial.X^8 + Polynomial.C (13/4 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1574.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1574.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1574.rational a+Real.sqrt 2*evalQPoly rf1574.irrational a)/evalQPoly rf1574.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1574,rf1531]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^1 + Polynomial.C (111/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-156/35 : ℚ)*Polynomial.X^3 + Polynomial.C (19/35 : ℚ)*Polynomial.X^4 + Polynomial.C (221/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-2999/35 : ℚ)*Polynomial.X^6 + Polynomial.C (564/7 : ℚ)*Polynomial.X^7 + Polynomial.C (1017/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-653/14 : ℚ)*Polynomial.X^9 + Polynomial.C (-397/14 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1560.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1560.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1560.rational a+Real.sqrt 2*evalQPoly rf1560.irrational a)/evalQPoly rf1560.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1560,rf1531]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (18/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-25/7 : ℚ)*Polynomial.X^3 + Polynomial.C (424/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-141/7 : ℚ)*Polynomial.X^5 + Polynomial.C (82/7 : ℚ)*Polynomial.X^6 + Polynomial.C (27/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^8 + Polynomial.C (-38/7 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1588.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1588.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1588.rational a+Real.sqrt 2*evalQPoly rf1588.irrational a)/evalQPoly rf1588.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1588,rf1531]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/5 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/35 : ℚ)*Polynomial.X^2 + Polynomial.C (9/7 : ℚ)*Polynomial.X^3 + Polynomial.C (86/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-271/35 : ℚ)*Polynomial.X^5 + Polynomial.C (97/35 : ℚ)*Polynomial.X^6 + Polynomial.C (29/5 : ℚ)*Polynomial.X^7 + Polynomial.C (7/2 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1617.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1617.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1617.rational a+Real.sqrt 2*evalQPoly rf1617.irrational a)/evalQPoly rf1617.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1617,rf1531]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-53/35 : ℚ)*Polynomial.X^3 + Polynomial.C (803/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-395/14 : ℚ)*Polynomial.X^5 + Polynomial.C (901/35 : ℚ)*Polynomial.X^6 + Polynomial.C (27/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-227/20 : ℚ)*Polynomial.X^8 + Polynomial.C (-243/28 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1602.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1602.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1602.rational a+Real.sqrt 2*evalQPoly rf1602.irrational a)/evalQPoly rf1602.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1602,rf1531]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (9/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-25/14 : ℚ)*Polynomial.X^2 + Polynomial.C (214/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-741/70 : ℚ)*Polynomial.X^4 + Polynomial.C (241/35 : ℚ)*Polynomial.X^5 + Polynomial.C (277/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-144/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-5/7 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1631.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1631.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1631.rational a+Real.sqrt 2*evalQPoly rf1631.irrational a)/evalQPoly rf1631.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1631,rf1531]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/5 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/35 : ℚ)*Polynomial.X^2 + Polynomial.C (9/7 : ℚ)*Polynomial.X^3 + Polynomial.C (86/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-271/35 : ℚ)*Polynomial.X^5 + Polynomial.C (97/35 : ℚ)*Polynomial.X^6 + Polynomial.C (29/5 : ℚ)*Polynomial.X^7 + Polynomial.C (7/2 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1617.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1617.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1617.rational a+Real.sqrt 2*evalQPoly rf1617.irrational a)/evalQPoly rf1617.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1617,rf1531]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd032
