import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even080
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1672.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (3 : ℚ)*Polynomial.X^3 + Polynomial.C (-17 : ℚ)*Polynomial.X^4 + Polynomial.C (38 : ℚ)*Polynomial.X^5 + Polynomial.C (-38 : ℚ)*Polynomial.X^6 + Polynomial.C (3 : ℚ)*Polynomial.X^7 + Polynomial.C (11 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1672.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1672.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1672.rational a+Real.sqrt 2*evalQPoly rf1672.irrational a)/evalQPoly rf1672.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1672,rf1672]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := 0
theorem eval1 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0013,rf1672]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^2 + Polynomial.C (3 : ℚ)*Polynomial.X^3 + Polynomial.C (-4 : ℚ)*Polynomial.X^4 + Polynomial.C (2 : ℚ)*Polynomial.X^5 + Polynomial.C (7/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1742.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1742.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1742.rational a+Real.sqrt 2*evalQPoly rf1742.irrational a)/evalQPoly rf1742.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1742,rf1672]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := 0
theorem eval3 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0013,rf1672]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3 : ℚ)*Polynomial.X^2 + Polynomial.C (17 : ℚ)*Polynomial.X^3 + Polynomial.C (-50 : ℚ)*Polynomial.X^4 + Polynomial.C (82 : ℚ)*Polynomial.X^5 + Polynomial.C (-79 : ℚ)*Polynomial.X^6 + Polynomial.C (33 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1718.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1718.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1718.rational a+Real.sqrt 2*evalQPoly rf1718.irrational a)/evalQPoly rf1718.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1718,rf1672]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf1672]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-4 : ℚ)*Polynomial.X^2 + Polynomial.C (9 : ℚ)*Polynomial.X^3 + Polynomial.C (-10 : ℚ)*Polynomial.X^4 + Polynomial.C (4 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1833.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1833.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1833.rational a+Real.sqrt 2*evalQPoly rf1833.irrational a)/evalQPoly rf1833.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1833,rf1672]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (6 : ℚ)*Polynomial.X^3 + Polynomial.C (-22 : ℚ)*Polynomial.X^4 + Polynomial.C (38 : ℚ)*Polynomial.X^5 + Polynomial.C (-22 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1787.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1787.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1787.rational a+Real.sqrt 2*evalQPoly rf1787.irrational a)/evalQPoly rf1787.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1787,rf1672]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := 0
theorem eval8 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0013,rf1672]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/4 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-5 : ℚ)*Polynomial.X^2 + Polynomial.C (8 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/4 : ℚ)*Polynomial.X^4
theorem eval9 (a : ℝ) (h : rf1902.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1902.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1902.rational a+Real.sqrt 2*evalQPoly rf1902.irrational a)/evalQPoly rf1902.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1902,rf1672]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (6 : ℚ)*Polynomial.X^2 + Polynomial.C (-22 : ℚ)*Polynomial.X^3 + Polynomial.C (38 : ℚ)*Polynomial.X^4 + Polynomial.C (-22 : ℚ)*Polynomial.X^5
theorem eval10 (a : ℝ) (h : rf1878.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1878.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1878.rational a+Real.sqrt 2*evalQPoly rf1878.irrational a)/evalQPoly rf1878.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1878,rf1672]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := 0
theorem eval11 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0013,rf1672]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even080
