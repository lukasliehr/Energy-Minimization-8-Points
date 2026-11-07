import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd027
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1526.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (113/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-57/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-779/140 : ℚ)*Polynomial.X^4 + Polynomial.C (1033/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-6501/140 : ℚ)*Polynomial.X^6 + Polynomial.C (963/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-289/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-328/35 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1526.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1526.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1526.rational a+Real.sqrt 2*evalQPoly rf1526.irrational a)/evalQPoly rf1526.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1526,rf1526]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-243/70 : ℚ)*Polynomial.X^3 + Polynomial.C (899/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-141/7 : ℚ)*Polynomial.X^5 + Polynomial.C (949/70 : ℚ)*Polynomial.X^6 + Polynomial.C (113/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-621/140 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1541.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1541.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1541.rational a+Real.sqrt 2*evalQPoly rf1541.irrational a)/evalQPoly rf1541.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1541,rf1526]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (23/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-39/35 : ℚ)*Polynomial.X^3 + Polynomial.C (437/140 : ℚ)*Polynomial.X^4 + Polynomial.C (1/10 : ℚ)*Polynomial.X^5 + Polynomial.C (-7/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1570.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1570.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1570.rational a+Real.sqrt 2*evalQPoly rf1570.irrational a)/evalQPoly rf1570.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1570,rf1526]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^1 + Polynomial.C (17/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-76/35 : ℚ)*Polynomial.X^3 + Polynomial.C (19/140 : ℚ)*Polynomial.X^4 + Polynomial.C (1691/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-9357/140 : ℚ)*Polynomial.X^6 + Polynomial.C (2467/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-5213/140 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1555.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1555.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1555.rational a+Real.sqrt 2*evalQPoly rf1555.irrational a)/evalQPoly rf1555.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1555,rf1526]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^3 + Polynomial.C (386/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-1019/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1261/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-586/35 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1583.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1583.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1583.rational a+Real.sqrt 2*evalQPoly rf1583.irrational a)/evalQPoly rf1583.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1583,rf1526]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/20 : ℚ)*Polynomial.X^0 + Polynomial.C (33/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/35 : ℚ)*Polynomial.X^3 + Polynomial.C (123/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-19/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1612.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1612.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1612.rational a+Real.sqrt 2*evalQPoly rf1612.irrational a)/evalQPoly rf1612.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1612,rf1526]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-111/140 : ℚ)*Polynomial.X^2 + Polynomial.C (44/35 : ℚ)*Polynomial.X^3 + Polynomial.C (1447/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-1094/35 : ℚ)*Polynomial.X^5 + Polynomial.C (5219/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-586/35 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1597.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1597.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1597.rational a+Real.sqrt 2*evalQPoly rf1597.irrational a)/evalQPoly rf1597.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1597,rf1526]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/14 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^2 + Polynomial.C (193/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-1019/70 : ℚ)*Polynomial.X^4 + Polynomial.C (1261/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-293/35 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1626.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1626.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1626.rational a+Real.sqrt 2*evalQPoly rf1626.irrational a)/evalQPoly rf1626.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1626,rf1526]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/20 : ℚ)*Polynomial.X^2 + Polynomial.C (3/5 : ℚ)*Polynomial.X^3 + Polynomial.C (17/28 : ℚ)*Polynomial.X^4 + Polynomial.C (19/14 : ℚ)*Polynomial.X^5 + Polynomial.C (5/4 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1640.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1640.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1640.rational a+Real.sqrt 2*evalQPoly rf1640.irrational a)/evalQPoly rf1640.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1640,rf1526]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd027
