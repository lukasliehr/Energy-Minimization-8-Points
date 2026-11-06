import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even051
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1322.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/28 : ℚ)*Polynomial.X^2 + Polynomial.C (53/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-82/119 : ℚ)*Polynomial.X^4 + Polynomial.C (211/238 : ℚ)*Polynomial.X^5 + Polynomial.C (487/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-1418/119 : ℚ)*Polynomial.X^7 + Polynomial.C (2552/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-5487/476 : ℚ)*Polynomial.X^9 + Polynomial.C (-3285/476 : ℚ)*Polynomial.X^10 + Polynomial.C (515/238 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1322.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1322.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1322.rational a+Real.sqrt 2*evalQPoly rf1322.irrational a)/evalQPoly rf1322.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1322,rf1322]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (2/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-31/119 : ℚ)*Polynomial.X^4 + Polynomial.C (157/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-256/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-316/119 : ℚ)*Polynomial.X^7 + Polynomial.C (207/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-835/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-134/17 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1341.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1341.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1341.rational a+Real.sqrt 2*evalQPoly rf1341.irrational a)/evalQPoly rf1341.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1341,rf1322]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^1 + Polynomial.C (16/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-82/119 : ℚ)*Polynomial.X^3 + Polynomial.C (123/119 : ℚ)*Polynomial.X^4 + Polynomial.C (271/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-1154/119 : ℚ)*Polynomial.X^6 + Polynomial.C (1112/119 : ℚ)*Polynomial.X^7 + Polynomial.C (183/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1377.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1377.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1377.rational a+Real.sqrt 2*evalQPoly rf1377.irrational a)/evalQPoly rf1377.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1377,rf1322]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^3 + Polynomial.C (9/119 : ℚ)*Polynomial.X^4 + Polynomial.C (6/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-18/17 : ℚ)*Polynomial.X^6 + Polynomial.C (11/119 : ℚ)*Polynomial.X^7 + Polynomial.C (3 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1431.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1431.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1431.rational a+Real.sqrt 2*evalQPoly rf1431.irrational a)/evalQPoly rf1431.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1431,rf1322]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (19/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-141/476 : ℚ)*Polynomial.X^2 + Polynomial.C (20/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-321/119 : ℚ)*Polynomial.X^4 + Polynomial.C (633/238 : ℚ)*Polynomial.X^5 + Polynomial.C (82/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-2976/119 : ℚ)*Polynomial.X^7 + Polynomial.C (21365/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-16757/476 : ℚ)*Polynomial.X^9 + Polynomial.C (1509/476 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf1358.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1358.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1358.rational a+Real.sqrt 2*evalQPoly rf1358.irrational a)/evalQPoly rf1358.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1358,rf1322]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (1/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^4 + Polynomial.C (207/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-536/119 : ℚ)*Polynomial.X^6 + Polynomial.C (39/119 : ℚ)*Polynomial.X^7 + Polynomial.C (284/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-385/17 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf1395.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1395.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1395.rational a+Real.sqrt 2*evalQPoly rf1395.irrational a)/evalQPoly rf1395.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1395,rf1322]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (101/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-256/119 : ℚ)*Polynomial.X^3 + Polynomial.C (146/119 : ℚ)*Polynomial.X^4 + Polynomial.C (767/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-2059/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2082/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-45/7 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1448.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1448.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1448.rational a+Real.sqrt 2*evalQPoly rf1448.irrational a)/evalQPoly rf1448.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1448,rf1322]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (9/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-117/238 : ℚ)*Polynomial.X^2 + Polynomial.C (347/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-431/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/238 : ℚ)*Polynomial.X^5 + Polynomial.C (417/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-1111/238 : ℚ)*Polynomial.X^7 + Polynomial.C (1762/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-2645/238 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf1412.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1412.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1412.rational a+Real.sqrt 2*evalQPoly rf1412.irrational a)/evalQPoly rf1412.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1412,rf1322]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^3 + Polynomial.C (41/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-134/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-54/119 : ℚ)*Polynomial.X^6 + Polynomial.C (79/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-21/17 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1466.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1466.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1466.rational a+Real.sqrt 2*evalQPoly rf1466.irrational a)/evalQPoly rf1466.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1466,rf1322]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (99/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-229/119 : ℚ)*Polynomial.X^3 + Polynomial.C (9/17 : ℚ)*Polynomial.X^4 + Polynomial.C (589/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-787/119 : ℚ)*Polynomial.X^6 + Polynomial.C (9/7 : ℚ)*Polynomial.X^7
theorem eval9 (a : ℝ) (h : rf1502.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1502.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1502.rational a+Real.sqrt 2*evalQPoly rf1502.irrational a)/evalQPoly rf1502.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1502,rf1322]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (9/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-26/119 : ℚ)*Polynomial.X^2 + Polynomial.C (71/238 : ℚ)*Polynomial.X^3 + Polynomial.C (321/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-1049/238 : ℚ)*Polynomial.X^5 + Polynomial.C (46/119 : ℚ)*Polynomial.X^6 + Polynomial.C (153/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-423/68 : ℚ)*Polynomial.X^8
theorem eval10 (a : ℝ) (h : rf1483.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1483.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1483.rational a+Real.sqrt 2*evalQPoly rf1483.irrational a)/evalQPoly rf1483.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1483,rf1322]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/119 : ℚ)*Polynomial.X^3 + Polynomial.C (40/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-156/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^6 + Polynomial.C (98/17 : ℚ)*Polynomial.X^7
theorem eval11 (a : ℝ) (h : rf1520.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1520.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1520.rational a+Real.sqrt 2*evalQPoly rf1520.irrational a)/evalQPoly rf1520.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1520,rf1322]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even051
