import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even034
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1065.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-401/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (75/782 : ℚ)*Polynomial.X^6 + Polynomial.C (-2795/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (271/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-10401/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (154611/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-13801/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (2297/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (15629/3910 : ℚ)*Polynomial.X^13 + Polynomial.C (-35257/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (1413/2380 : ℚ)*Polynomial.X^15 + Polynomial.C (25939/27370 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1065.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1065.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1065.rational a+Real.sqrt 2*evalQPoly rf1065.irrational a)/evalQPoly rf1065.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1065,rf1065]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (3149/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-582/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (1301/3220 : ℚ)*Polynomial.X^7 + Polynomial.C (-3457/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-76133/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (26539/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-434751/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (98491/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-34081/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-11439/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (27/85 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1080.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1080.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1080.rational a+Real.sqrt 2*evalQPoly rf1080.irrational a)/evalQPoly rf1080.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1080,rf1065]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (2/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (223/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-9053/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (8604/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-2019/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (513/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (59083/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-22767/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (5599/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-7366/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-275/644 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1108.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1108.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1108.rational a+Real.sqrt 2*evalQPoly rf1108.irrational a)/evalQPoly rf1108.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1108,rf1065]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (0 : ℚ)*Polynomial.X^5 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-2/805 : ℚ)*Polynomial.X^7 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-402/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-106/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (1514/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-1882/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (6/115 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1150.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1150.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1150.rational a+Real.sqrt 2*evalQPoly rf1150.irrational a)/evalQPoly rf1150.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1150,rf1065]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (209/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1138/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (3517/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (2815/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (-344/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-1181/1564 : ℚ)*Polynomial.X^9 + Polynomial.C (85996/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-136076/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (55011/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (28699/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (-165479/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (161907/54740 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1093.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1093.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1093.rational a+Real.sqrt 2*evalQPoly rf1093.irrational a)/evalQPoly rf1093.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1093,rf1065]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (1/4760 : ℚ)*Polynomial.X^2 + Polynomial.C (88/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3127/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (1307/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-4757/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (116/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-60019/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-121627/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (847291/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-163298/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (134578/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-55213/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (2383/3910 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1122.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1122.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1122.rational a+Real.sqrt 2*evalQPoly rf1122.irrational a)/evalQPoly rf1122.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1122,rf1065]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-228/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1433/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-236/595 : ℚ)*Polynomial.X^6 + Polynomial.C (1341/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-4/23 : ℚ)*Polynomial.X^8 + Polynomial.C (14649/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-2384/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-9937/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (5072/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (-2917/3220 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1163.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1163.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1163.rational a+Real.sqrt 2*evalQPoly rf1163.irrational a)/evalQPoly rf1163.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1163,rf1065]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-383/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (7519/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-8044/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (19174/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-4237/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-65827/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1002/161 : ℚ)*Polynomial.X^10 + Polynomial.C (-93676/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (59497/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (4353/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-18238/13685 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1135.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1135.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1135.rational a+Real.sqrt 2*evalQPoly rf1135.irrational a)/evalQPoly rf1135.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1135,rf1065]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-351/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (234/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-1366/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (15059/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-2424/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-14903/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (27211/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-267517/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (26481/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-7329/3910 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1177.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1177.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1177.rational a+Real.sqrt 2*evalQPoly rf1177.irrational a)/evalQPoly rf1177.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1177,rf1065]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (133/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (-634/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (7662/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-344/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-16672/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (30811/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (3357/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-41043/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (369/322 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1205.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1205.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1205.rational a+Real.sqrt 2*evalQPoly rf1205.irrational a)/evalQPoly rf1205.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1205,rf1065]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (7/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-159/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-309/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (5458/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-12567/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1838/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (254693/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-46611/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-4349/1190 : ℚ)*Polynomial.X^11 + Polynomial.C (72581/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-22397/7820 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1190.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1190.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1190.rational a+Real.sqrt 2*evalQPoly rf1190.irrational a)/evalQPoly rf1190.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1190,rf1065]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (2441/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-3569/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (4076/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (45/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-98453/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (32122/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-10751/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-1414/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (917/1955 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1219.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1219.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1219.rational a+Real.sqrt 2*evalQPoly rf1219.irrational a)/evalQPoly rf1219.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1219,rf1065]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even034
