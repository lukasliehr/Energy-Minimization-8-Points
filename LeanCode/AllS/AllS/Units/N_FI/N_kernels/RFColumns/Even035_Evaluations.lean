import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even035
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1066.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (2 : ℚ)*Polynomial.X^3 + Polynomial.C (-6 : ℚ)*Polynomial.X^4 + Polynomial.C (2 : ℚ)*Polynomial.X^5 + Polynomial.C (2 : ℚ)*Polynomial.X^6
theorem eval0 (a : ℝ) (h : rf1066.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1066.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1066.rational a+Real.sqrt 2*evalQPoly rf1066.irrational a)/evalQPoly rf1066.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1066,rf1066]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := 0
theorem eval1 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0013,rf1066]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^2 + Polynomial.C (1 : ℚ)*Polynomial.X^3 + Polynomial.C (1/2 : ℚ)*Polynomial.X^4
theorem eval2 (a : ℝ) (h : rf1109.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1109.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1109.rational a+Real.sqrt 2*evalQPoly rf1109.irrational a)/evalQPoly rf1109.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1109,rf1066]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := 0
theorem eval3 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0013,rf1066]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (6 : ℚ)*Polynomial.X^3 + Polynomial.C (-10 : ℚ)*Polynomial.X^4 + Polynomial.C (6 : ℚ)*Polynomial.X^5
theorem eval4 (a : ℝ) (h : rf1094.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1094.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1094.rational a+Real.sqrt 2*evalQPoly rf1094.irrational a)/evalQPoly rf1094.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1094,rf1066]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf1066]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-2 : ℚ)*Polynomial.X^2 + Polynomial.C (1 : ℚ)*Polynomial.X^3
theorem eval6 (a : ℝ) (h : rf1164.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1164.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1164.rational a+Real.sqrt 2*evalQPoly rf1164.irrational a)/evalQPoly rf1164.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1164,rf1066]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (4 : ℚ)*Polynomial.X^3 + Polynomial.C (-4 : ℚ)*Polynomial.X^4
theorem eval7 (a : ℝ) (h : rf1136.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1136.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1136.rational a+Real.sqrt 2*evalQPoly rf1136.irrational a)/evalQPoly rf1136.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1136,rf1066]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := 0
theorem eval8 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0013,rf1066]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/2 : ℚ)*Polynomial.X^0 + Polynomial.C (1 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/2 : ℚ)*Polynomial.X^2
theorem eval9 (a : ℝ) (h : rf1206.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1206.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1206.rational a+Real.sqrt 2*evalQPoly rf1206.irrational a)/evalQPoly rf1206.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1206,rf1066]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (4 : ℚ)*Polynomial.X^2 + Polynomial.C (-4 : ℚ)*Polynomial.X^3
theorem eval10 (a : ℝ) (h : rf1191.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1191.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1191.rational a+Real.sqrt 2*evalQPoly rf1191.irrational a)/evalQPoly rf1191.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1191,rf1066]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := 0
theorem eval11 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0013,rf1066]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even035
