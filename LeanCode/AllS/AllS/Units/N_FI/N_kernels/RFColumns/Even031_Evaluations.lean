import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even031
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1062.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/119 : ℚ)*Polynomial.X^2 + Polynomial.C (4/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-43/34 : ℚ)*Polynomial.X^4 + Polynomial.C (1147/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-301/34 : ℚ)*Polynomial.X^6 + Polynomial.C (232/119 : ℚ)*Polynomial.X^7 + Polynomial.C (3453/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-5703/476 : ℚ)*Polynomial.X^9 + Polynomial.C (-1389/238 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1062.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1062.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1062.rational a+Real.sqrt 2*evalQPoly rf1062.irrational a)/evalQPoly rf1062.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1062,rf1062]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (2/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-31/119 : ℚ)*Polynomial.X^3 + Polynomial.C (157/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-256/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-316/119 : ℚ)*Polynomial.X^6 + Polynomial.C (207/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-835/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-134/17 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1077.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1077.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1077.rational a+Real.sqrt 2*evalQPoly rf1077.irrational a)/evalQPoly rf1077.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1077,rf1062]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^1 + Polynomial.C (15/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-76/119 : ℚ)*Polynomial.X^3 + Polynomial.C (192/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-313/119 : ℚ)*Polynomial.X^5 + Polynomial.C (183/119 : ℚ)*Polynomial.X^6 + Polynomial.C (230/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1105.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1105.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1105.rational a+Real.sqrt 2*evalQPoly rf1105.irrational a)/evalQPoly rf1105.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1105,rf1062]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^2 + Polynomial.C (9/119 : ℚ)*Polynomial.X^3 + Polynomial.C (6/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-18/17 : ℚ)*Polynomial.X^5 + Polynomial.C (11/119 : ℚ)*Polynomial.X^6 + Polynomial.C (3 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1147.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1147.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1147.rational a+Real.sqrt 2*evalQPoly rf1147.irrational a)/evalQPoly rf1147.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1147,rf1062]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (19/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/17 : ℚ)*Polynomial.X^2 + Polynomial.C (19/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-563/238 : ℚ)*Polynomial.X^4 + Polynomial.C (111/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-547/119 : ℚ)*Polynomial.X^6 + Polynomial.C (197/119 : ℚ)*Polynomial.X^7 + Polynomial.C (6143/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-9677/476 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1090.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1090.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1090.rational a+Real.sqrt 2*evalQPoly rf1090.irrational a)/evalQPoly rf1090.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1090,rf1062]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^3 + Polynomial.C (207/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-536/119 : ℚ)*Polynomial.X^5 + Polynomial.C (39/119 : ℚ)*Polynomial.X^6 + Polynomial.C (284/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-385/17 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1119.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1119.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1119.rational a+Real.sqrt 2*evalQPoly rf1119.irrational a)/evalQPoly rf1119.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1119,rf1062]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-15/119 : ℚ)*Polynomial.X^1 + Polynomial.C (10/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/17 : ℚ)*Polynomial.X^3 + Polynomial.C (29/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-39/119 : ℚ)*Polynomial.X^5 + Polynomial.C (236/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1160.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1160.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1160.rational a+Real.sqrt 2*evalQPoly rf1160.irrational a)/evalQPoly rf1160.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1160,rf1062]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-3/476 : ℚ)*Polynomial.X^0 + Polynomial.C (23/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-57/119 : ℚ)*Polynomial.X^2 + Polynomial.C (209/238 : ℚ)*Polynomial.X^3 + Polynomial.C (11/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-193/34 : ℚ)*Polynomial.X^5 + Polynomial.C (1641/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-439/34 : ℚ)*Polynomial.X^7 + Polynomial.C (2921/476 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1132.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1132.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1132.rational a+Real.sqrt 2*evalQPoly rf1132.irrational a)/evalQPoly rf1132.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1132,rf1062]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^2 + Polynomial.C (41/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-134/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-54/119 : ℚ)*Polynomial.X^5 + Polynomial.C (79/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-21/17 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1174.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1174.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1174.rational a+Real.sqrt 2*evalQPoly rf1174.irrational a)/evalQPoly rf1174.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1174,rf1062]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^1 + Polynomial.C (108/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-40/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-502/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1012/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-40/7 : ℚ)*Polynomial.X^6
theorem eval9 (a : ℝ) (h : rf1202.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1202.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1202.rational a+Real.sqrt 2*evalQPoly rf1202.irrational a)/evalQPoly rf1202.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1202,rf1062]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (13/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-115/238 : ℚ)*Polynomial.X^3 + Polynomial.C (501/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-209/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-149/34 : ℚ)*Polynomial.X^6 + Polynomial.C (273/34 : ℚ)*Polynomial.X^7
theorem eval10 (a : ℝ) (h : rf1187.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1187.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1187.rational a+Real.sqrt 2*evalQPoly rf1187.irrational a)/evalQPoly rf1187.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1187,rf1062]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/119 : ℚ)*Polynomial.X^2 + Polynomial.C (40/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-156/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^5 + Polynomial.C (98/17 : ℚ)*Polynomial.X^6
theorem eval11 (a : ℝ) (h : rf1216.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1216.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1216.rational a+Real.sqrt 2*evalQPoly rf1216.irrational a)/evalQPoly rf1216.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1216,rf1062]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even031
