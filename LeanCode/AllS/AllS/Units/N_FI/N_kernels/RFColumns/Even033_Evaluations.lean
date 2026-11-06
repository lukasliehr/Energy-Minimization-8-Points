import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even033
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1064.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/17 : ℚ)*Polynomial.X^2 + Polynomial.C (55/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-77/34 : ℚ)*Polynomial.X^4 + Polynomial.C (295/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-82/17 : ℚ)*Polynomial.X^6 + Polynomial.C (113/68 : ℚ)*Polynomial.X^7 + Polynomial.C (47/34 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1064.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1064.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1064.rational a+Real.sqrt 2*evalQPoly rf1064.irrational a)/evalQPoly rf1064.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1064,rf1064]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/34 : ℚ)*Polynomial.X^2 + Polynomial.C (12/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-63/34 : ℚ)*Polynomial.X^5 + Polynomial.C (33/34 : ℚ)*Polynomial.X^6 + Polynomial.C (33/17 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1079.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1079.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1079.rational a+Real.sqrt 2*evalQPoly rf1079.irrational a)/evalQPoly rf1079.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1079,rf1064]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (13/34 : ℚ)*Polynomial.X^2 + Polynomial.C (-25/17 : ℚ)*Polynomial.X^3 + Polynomial.C (40/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-41/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1107.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1107.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1107.rational a+Real.sqrt 2*evalQPoly rf1107.irrational a)/evalQPoly rf1107.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1107,rf1064]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^3 + Polynomial.C (10/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-1 : ℚ)*Polynomial.X^5
theorem eval3 (a : ℝ) (h : rf1149.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1149.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1149.rational a+Real.sqrt 2*evalQPoly rf1149.irrational a)/evalQPoly rf1149.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1149,rf1064]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (13/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-71/68 : ℚ)*Polynomial.X^2 + Polynomial.C (233/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-487/68 : ℚ)*Polynomial.X^4 + Polynomial.C (671/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-593/68 : ℚ)*Polynomial.X^6 + Polynomial.C (299/68 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1092.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1092.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1092.rational a+Real.sqrt 2*evalQPoly rf1092.irrational a)/evalQPoly rf1092.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1092,rf1064]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (9/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/34 : ℚ)*Polynomial.X^2 + Polynomial.C (10/17 : ℚ)*Polynomial.X^3 + Polynomial.C (61/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-161/34 : ℚ)*Polynomial.X^5 + Polynomial.C (147/34 : ℚ)*Polynomial.X^6
theorem eval5 (a : ℝ) (h : rf1121.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1121.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1121.rational a+Real.sqrt 2*evalQPoly rf1121.irrational a)/evalQPoly rf1121.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1121,rf1064]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/17 : ℚ)*Polynomial.X^1 + Polynomial.C (32/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-71/17 : ℚ)*Polynomial.X^3 + Polynomial.C (159/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-2 : ℚ)*Polynomial.X^5
theorem eval6 (a : ℝ) (h : rf1162.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1162.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1162.rational a+Real.sqrt 2*evalQPoly rf1162.irrational a)/evalQPoly rf1162.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1162,rf1064]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (4/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^2 + Polynomial.C (56/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-363/68 : ℚ)*Polynomial.X^4 + Polynomial.C (96/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-239/68 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1134.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1134.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1134.rational a+Real.sqrt 2*evalQPoly rf1134.irrational a)/evalQPoly rf1134.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1134,rf1064]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/17 : ℚ)*Polynomial.X^2 + Polynomial.C (10/17 : ℚ)*Polynomial.X^3 + Polynomial.C (21/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-49/17 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1176.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1176.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1176.rational a+Real.sqrt 2*evalQPoly rf1176.irrational a)/evalQPoly rf1176.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1176,rf1064]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/17 : ℚ)*Polynomial.X^1 + Polynomial.C (31/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-59/17 : ℚ)*Polynomial.X^3 + Polynomial.C (5/2 : ℚ)*Polynomial.X^4
theorem eval9 (a : ℝ) (h : rf1204.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1204.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1204.rational a+Real.sqrt 2*evalQPoly rf1204.irrational a)/evalQPoly rf1204.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1204,rf1064]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^2 + Polynomial.C (5/17 : ℚ)*Polynomial.X^3 + Polynomial.C (24/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-77/34 : ℚ)*Polynomial.X^5
theorem eval10 (a : ℝ) (h : rf1189.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1189.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1189.rational a+Real.sqrt 2*evalQPoly rf1189.irrational a)/evalQPoly rf1189.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1189,rf1064]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/17 : ℚ)*Polynomial.X^2 + Polynomial.C (43/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-115/34 : ℚ)*Polynomial.X^4
theorem eval11 (a : ℝ) (h : rf1218.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1218.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1218.rational a+Real.sqrt 2*evalQPoly rf1218.irrational a)/evalQPoly rf1218.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1218,rf1064]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even033
