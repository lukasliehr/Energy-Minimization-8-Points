import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even028
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1059.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^1 + Polynomial.C (10/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-146/119 : ℚ)*Polynomial.X^4 + Polynomial.C (27/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1466/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-2113/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-2510/119 : ℚ)*Polynomial.X^8 + Polynomial.C (5034/119 : ℚ)*Polynomial.X^9 + Polynomial.C (1308/119 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1059.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1059.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1059.rational a+Real.sqrt 2*evalQPoly rf1059.irrational a)/evalQPoly rf1059.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1059,rf1059]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/238 : ℚ)*Polynomial.X^1 + Polynomial.C (67/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-269/238 : ℚ)*Polynomial.X^3 + Polynomial.C (27/34 : ℚ)*Polynomial.X^4 + Polynomial.C (145/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-1611/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-1595/238 : ℚ)*Polynomial.X^7 + Polynomial.C (1259/238 : ℚ)*Polynomial.X^8 + Polynomial.C (397/17 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1074.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1074.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1074.rational a+Real.sqrt 2*evalQPoly rf1074.irrational a)/evalQPoly rf1074.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1074,rf1059]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/17 : ℚ)*Polynomial.X^2 + Polynomial.C (25/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-250/119 : ℚ)*Polynomial.X^4 + Polynomial.C (33/119 : ℚ)*Polynomial.X^5 + Polynomial.C (858/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-245/17 : ℚ)*Polynomial.X^7 + Polynomial.C (10/7 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1102.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1102.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1102.rational a+Real.sqrt 2*evalQPoly rf1102.irrational a)/evalQPoly rf1102.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1102,rf1059]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-40/119 : ℚ)*Polynomial.X^2 + Polynomial.C (155/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-216/119 : ℚ)*Polynomial.X^4 + Polynomial.C (9/119 : ℚ)*Polynomial.X^5 + Polynomial.C (64/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-17 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1144.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1144.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1144.rational a+Real.sqrt 2*evalQPoly rf1144.irrational a)/evalQPoly rf1144.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1144,rf1059]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-16/119 : ℚ)*Polynomial.X^1 + Polynomial.C (89/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-174/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-185/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1086/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-37/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-3146/119 : ℚ)*Polynomial.X^7 + Polynomial.C (156/17 : ℚ)*Polynomial.X^8 + Polynomial.C (5386/119 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1087.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1087.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1087.rational a+Real.sqrt 2*evalQPoly rf1087.irrational a)/evalQPoly rf1087.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1087,rf1059]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/238 : ℚ)*Polynomial.X^1 + Polynomial.C (30/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-143/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-195/119 : ℚ)*Polynomial.X^4 + Polynomial.C (2631/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-1322/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-5869/238 : ℚ)*Polynomial.X^7 + Polynomial.C (1787/34 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1116.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1116.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1116.rational a+Real.sqrt 2*evalQPoly rf1116.irrational a)/evalQPoly rf1116.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1116,rf1059]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/119 : ℚ)*Polynomial.X^0 + Polynomial.C (44/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-191/119 : ℚ)*Polynomial.X^2 + Polynomial.C (216/119 : ℚ)*Polynomial.X^3 + Polynomial.C (239/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-636/119 : ℚ)*Polynomial.X^5 + Polynomial.C (149/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-72/7 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1157.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1157.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1157.rational a+Real.sqrt 2*evalQPoly rf1157.irrational a)/evalQPoly rf1157.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1157,rf1059]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/119 : ℚ)*Polynomial.X^1 + Polynomial.C (160/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-367/119 : ℚ)*Polynomial.X^3 + Polynomial.C (44/17 : ℚ)*Polynomial.X^4 + Polynomial.C (149/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-3368/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2043/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-814/119 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1129.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1129.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1129.rational a+Real.sqrt 2*evalQPoly rf1129.irrational a)/evalQPoly rf1129.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1129,rf1059]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/17 : ℚ)*Polynomial.X^3 + Polynomial.C (326/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-235/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-175/17 : ℚ)*Polynomial.X^6 + Polynomial.C (56/17 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1171.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1171.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1171.rational a+Real.sqrt 2*evalQPoly rf1171.irrational a)/evalQPoly rf1171.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1171,rf1059]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-4/119 : ℚ)*Polynomial.X^0 + Polynomial.C (8/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-216/119 : ℚ)*Polynomial.X^2 + Polynomial.C (16/17 : ℚ)*Polynomial.X^3 + Polynomial.C (652/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-1160/119 : ℚ)*Polynomial.X^5 + Polynomial.C (48/7 : ℚ)*Polynomial.X^6
theorem eval9 (a : ℝ) (h : rf1199.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1199.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1199.rational a+Real.sqrt 2*evalQPoly rf1199.irrational a)/evalQPoly rf1199.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1199,rf1059]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-16/119 : ℚ)*Polynomial.X^1 + Polynomial.C (69/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-19/17 : ℚ)*Polynomial.X^4 + Polynomial.C (592/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-897/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-228/17 : ℚ)*Polynomial.X^7
theorem eval10 (a : ℝ) (h : rf1184.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1184.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1184.rational a+Real.sqrt 2*evalQPoly rf1184.irrational a)/evalQPoly rf1184.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1184,rf1059]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (2/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/119 : ℚ)*Polynomial.X^3 + Polynomial.C (661/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-274/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-449/34 : ℚ)*Polynomial.X^6
theorem eval11 (a : ℝ) (h : rf1213.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1213.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1213.rational a+Real.sqrt 2*evalQPoly rf1213.irrational a)/evalQPoly rf1213.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1213,rf1059]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even028
