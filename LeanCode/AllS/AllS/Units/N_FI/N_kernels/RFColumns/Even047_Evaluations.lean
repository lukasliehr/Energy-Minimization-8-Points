import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even047
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1318.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/230 : ℚ)*Polynomial.X^4 + Polynomial.C (691/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-953/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (3627/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (7577/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-599747/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (138109/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-87104/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-373291/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (1393157/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (13063/3220 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1318.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1318.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1318.rational a+Real.sqrt 2*evalQPoly rf1318.irrational a)/evalQPoly rf1318.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1318,rf1318]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (39/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-37/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (288/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-19/391 : ℚ)*Polynomial.X^7 + Polynomial.C (-951/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (14286/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (26157/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-164973/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-2103/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (37/5 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1337.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1337.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1337.rational a+Real.sqrt 2*evalQPoly rf1337.irrational a)/evalQPoly rf1337.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1337,rf1318]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (1707/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-1861/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (163/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (18779/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-14347/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (72441/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (178611/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-27575/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (211/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1373.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1373.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1373.rational a+Real.sqrt 2*evalQPoly rf1373.irrational a)/evalQPoly rf1373.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1373,rf1318]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (41/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (73/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^6 + Polynomial.C (1077/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-1291/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-10273/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (58516/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-528/115 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1427.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1427.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1427.rational a+Real.sqrt 2*evalQPoly rf1427.irrational a)/evalQPoly rf1427.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1427,rf1318]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/6440 : ℚ)*Polynomial.X^1 + Polynomial.C (5/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (389/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-7961/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (1933/6440 : ℚ)*Polynomial.X^5 + Polynomial.C (-3377/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (461/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (33347/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-33729/4760 : ℚ)*Polynomial.X^9 + Polynomial.C (915617/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-966859/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-337367/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (101179/6440 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1354.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1354.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1354.rational a+Real.sqrt 2*evalQPoly rf1354.irrational a)/evalQPoly rf1354.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1354,rf1318]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (12/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-199/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (402/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-1557/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (8966/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-33539/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (45646/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (123883/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-330/17 : ℚ)*Polynomial.X^11 + Polynomial.C (4123/230 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1391.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1391.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1391.rational a+Real.sqrt 2*evalQPoly rf1391.irrational a)/evalQPoly rf1391.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1391,rf1318]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (1/1955 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-181/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (81/391 : ℚ)*Polynomial.X^4 + Polynomial.C (-6334/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-148/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (33479/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-28249/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (56411/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (13528/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-4477/1610 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1444.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1444.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1444.rational a+Real.sqrt 2*evalQPoly rf1444.irrational a)/evalQPoly rf1444.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1444,rf1318]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (137/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-19361/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (6751/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-5352/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-2689/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (44237/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (27613/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-29163/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (128461/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-19379/6440 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1408.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1408.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1408.rational a+Real.sqrt 2*evalQPoly rf1408.irrational a)/evalQPoly rf1408.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1408,rf1318]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^3 + Polynomial.C (118/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-824/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (4127/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-11279/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (4702/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (6156/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-137063/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (171/230 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1462.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1462.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1462.rational a+Real.sqrt 2*evalQPoly rf1462.irrational a)/evalQPoly rf1462.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1462,rf1318]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/119 : ℚ)*Polynomial.X^3 + Polynomial.C (8609/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-1957/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (197/1190 : ℚ)*Polynomial.X^6 + Polynomial.C (24606/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-112911/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-24827/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (1227/644 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1498.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1498.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1498.rational a+Real.sqrt 2*evalQPoly rf1498.irrational a)/evalQPoly rf1498.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1498,rf1318]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (143/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-2439/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1707/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (2281/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-35243/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-8423/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (33857/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-9477/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-2357/460 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1479.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1479.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1479.rational a+Real.sqrt 2*evalQPoly rf1479.irrational a)/evalQPoly rf1479.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1479,rf1318]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-18/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (12/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-62/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (858/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-8718/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (15212/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (28062/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-573/115 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1516.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1516.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1516.rational a+Real.sqrt 2*evalQPoly rf1516.irrational a)/evalQPoly rf1516.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1516,rf1318]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even047
