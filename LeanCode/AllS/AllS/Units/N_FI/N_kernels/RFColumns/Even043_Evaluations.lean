import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even043
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1314.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (71/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (39/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-10539/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (63011/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-14957/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (19309/1190 : ℚ)*Polynomial.X^9 + Polynomial.C (-517511/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (27171/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (518939/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-130265/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-4051/782 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1314.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1314.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1314.rational a+Real.sqrt 2*evalQPoly rf1314.irrational a)/evalQPoly rf1314.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1314,rf1314]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (15/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-227/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-61/595 : ℚ)*Polynomial.X^5 + Polynomial.C (9599/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-26578/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (25409/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (102829/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-53487/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (201723/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-144/17 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1333.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1333.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1333.rational a+Real.sqrt 2*evalQPoly rf1333.irrational a)/evalQPoly rf1333.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1333,rf1314]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (48/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-111/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (-1144/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (26561/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-51584/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (205119/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-100888/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (60633/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (10208/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-135/92 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1369.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1369.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1369.rational a+Real.sqrt 2*evalQPoly rf1369.irrational a)/evalQPoly rf1369.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1369,rf1314]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (-29/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (131/805 : ℚ)*Polynomial.X^6 + Polynomial.C (-2521/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (1212/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (8383/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-90053/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (317/92 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1423.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1423.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1423.rational a+Real.sqrt 2*evalQPoly rf1423.irrational a)/evalQPoly rf1423.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1423,rf1314]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/2380 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/322 : ℚ)*Polynomial.X^3 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (7409/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-26581/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (49481/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-47247/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (812033/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-978941/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (196179/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (180997/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-31803/1564 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1350.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1350.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1350.rational a+Real.sqrt 2*evalQPoly rf1350.irrational a)/evalQPoly rf1350.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1350,rf1314]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-41/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (3/595 : ℚ)*Polynomial.X^3 + Polynomial.C (-159/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-1977/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (25671/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-40228/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (124077/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (5157/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-60101/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (468283/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-36089/1564 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1387.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1387.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1387.rational a+Real.sqrt 2*evalQPoly rf1387.irrational a)/evalQPoly rf1387.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1387,rf1314]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1564 : ℚ)*Polynomial.X^2 + Polynomial.C (29/1610 : ℚ)*Polynomial.X^3 + Polynomial.C (-361/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-229/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (38427/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-59208/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (416937/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-118434/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (57465/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-31/46 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1440.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1440.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1440.rational a+Real.sqrt 2*evalQPoly rf1440.irrational a)/evalQPoly rf1440.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1440,rf1314]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-653/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (283/3220 : ℚ)*Polynomial.X^4 + Polynomial.C (-7929/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (10063/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-11813/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (329757/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-668509/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (421047/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-565953/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (5987/1564 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1404.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1404.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1404.rational a+Real.sqrt 2*evalQPoly rf1404.irrational a)/evalQPoly rf1404.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1404,rf1314]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (27/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-281/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-82/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (4461/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-1353/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (1437/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (4286/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-275591/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (27101/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-2863/1564 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1458.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1458.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1458.rational a+Real.sqrt 2*evalQPoly rf1458.irrational a)/evalQPoly rf1458.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1458,rf1314]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (11/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (358/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-509/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (7867/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-2476/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (40118/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-144743/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (5703/1190 : ℚ)*Polynomial.X^9 + Polynomial.C (-33/23 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1494.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1494.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1494.rational a+Real.sqrt 2*evalQPoly rf1494.irrational a)/evalQPoly rf1494.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1494,rf1314]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-369/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (301/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (-2013/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (2361/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-4033/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (48219/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (27411/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-356667/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (5841/782 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1475.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1475.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1475.rational a+Real.sqrt 2*evalQPoly rf1475.irrational a)/evalQPoly rf1475.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1475,rf1314]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (31/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-48/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-76/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (3226/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-9389/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (10656/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (12368/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-67593/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (4561/782 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1512.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1512.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1512.rational a+Real.sqrt 2*evalQPoly rf1512.irrational a)/evalQPoly rf1512.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1512,rf1314]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even043
