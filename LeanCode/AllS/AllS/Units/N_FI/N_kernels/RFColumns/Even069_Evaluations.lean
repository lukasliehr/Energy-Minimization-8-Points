import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even069
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1661.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (1/1190 : ℚ)*Polynomial.X^3 + Polynomial.C (447/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-2319/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (52427/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-126447/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (6911/782 : ℚ)*Polynomial.X^8 + Polynomial.C (-1315411/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (673473/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (-533794/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-130447/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (44816/595 : ℚ)*Polynomial.X^13 + Polynomial.C (-259811/6440 : ℚ)*Polynomial.X^14 + Polynomial.C (-9713/460 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1661.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1661.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1661.rational a+Real.sqrt 2*evalQPoly rf1661.irrational a)/evalQPoly rf1661.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1661,rf1661]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-167/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (41/2380 : ℚ)*Polynomial.X^4 + Polynomial.C (123/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (-8501/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (86661/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-41173/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (150077/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (137639/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-2982211/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (434853/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (14901/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-323/10 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1685.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1685.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1685.rational a+Real.sqrt 2*evalQPoly rf1685.irrational a)/evalQPoly rf1685.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1685,rf1661]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (53/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/644 : ℚ)*Polynomial.X^3 + Polynomial.C (-75/1564 : ℚ)*Polynomial.X^4 + Polynomial.C (41427/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-37531/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (815/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-217589/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (351219/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-1021327/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (17213/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (741563/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-841/184 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1731.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1731.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1731.rational a+Real.sqrt 2*evalQPoly rf1731.irrational a)/evalQPoly rf1731.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1731,rf1661]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-12/805 : ℚ)*Polynomial.X^5 + Polynomial.C (-18/805 : ℚ)*Polynomial.X^6 + Polynomial.C (1726/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-330/161 : ℚ)*Polynomial.X^8 + Polynomial.C (27588/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (45139/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-180539/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (1521/115 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1800.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1800.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1800.rational a+Real.sqrt 2*evalQPoly rf1800.irrational a)/evalQPoly rf1800.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1800,rf1661]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-137/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/230 : ℚ)*Polynomial.X^3 + Polynomial.C (1755/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-3019/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (9957/4760 : ℚ)*Polynomial.X^6 + Polynomial.C (-63/17 : ℚ)*Polynomial.X^7 + Polynomial.C (349873/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-434453/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (4036173/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-200603/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (44841/3220 : ℚ)*Polynomial.X^12 + Polynomial.C (1860977/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-70849/920 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1707.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1707.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1707.rational a+Real.sqrt 2*evalQPoly rf1707.irrational a)/evalQPoly rf1707.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1707,rf1661]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (223/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (379/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-9999/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (12056/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-184811/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (208433/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (37473/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-238318/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (563617/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-42077/460 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1754.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1754.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1754.rational a+Real.sqrt 2*evalQPoly rf1754.irrational a)/evalQPoly rf1754.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1754,rf1661]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/15640 : ℚ)*Polynomial.X^0 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (37/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (771/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-47809/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (18679/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-23938/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-72/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-537/952 : ℚ)*Polynomial.X^8 + Polynomial.C (381573/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-878681/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (356553/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-4077/920 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1822.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1822.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1822.rational a+Real.sqrt 2*evalQPoly rf1822.irrational a)/evalQPoly rf1822.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1822,rf1661]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/21896 : ℚ)*Polynomial.X^0 + Polynomial.C (2/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (-15/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-2201/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (37993/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-1945/1564 : ℚ)*Polynomial.X^5 + Polynomial.C (53471/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (27219/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1344579/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (131679/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-3241667/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (720071/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-857165/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (6567/460 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1776.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1776.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1776.rational a+Real.sqrt 2*evalQPoly rf1776.irrational a)/evalQPoly rf1776.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1776,rf1661]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (213/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-117/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-4619/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (31267/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-18119/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (20151/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (271221/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-248361/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (1466769/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-2999/460 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1845.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1845.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1845.rational a+Real.sqrt 2*evalQPoly rf1845.irrational a)/evalQPoly rf1845.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1845,rf1661]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/10948 : ℚ)*Polynomial.X^0 + Polynomial.C (-73/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (33/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (55/644 : ℚ)*Polynomial.X^3 + Polynomial.C (-15839/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (38963/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (125/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-222661/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (1119193/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-276825/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (42283/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-611/92 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1891.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1891.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1891.rational a+Real.sqrt 2*evalQPoly rf1891.irrational a)/evalQPoly rf1891.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1891,rf1661]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-384/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (19169/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-855/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-1359/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (53594/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-658817/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (2103/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (182253/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-11346/391 : ℚ)*Polynomial.X^11 + Polynomial.C (26453/920 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1867.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1867.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1867.rational a+Real.sqrt 2*evalQPoly rf1867.irrational a)/evalQPoly rf1867.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1867,rf1661]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (53/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (2/391 : ℚ)*Polynomial.X^4 + Polynomial.C (-1997/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (12762/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-37189/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (41586/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (115657/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-39316/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (5187/230 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1914.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1914.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1914.rational a+Real.sqrt 2*evalQPoly rf1914.irrational a)/evalQPoly rf1914.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1914,rf1661]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even069
