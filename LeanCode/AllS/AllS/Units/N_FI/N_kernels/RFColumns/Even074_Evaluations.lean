import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even074
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1666.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (33/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (1313/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-4793/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (103237/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-44281/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (111075/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-148881/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (25693/6440 : ℚ)*Polynomial.X^11 + Polynomial.C (-60623/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (481991/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-82479/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (236563/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (517/920 : ℚ)*Polynomial.X^16 + Polynomial.C (-362167/109480 : ℚ)*Polynomial.X^17 + Polynomial.C (-9795/10948 : ℚ)*Polynomial.X^18
theorem eval0 (a : ℝ) (h : rf1666.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1666.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1666.rational a+Real.sqrt 2*evalQPoly rf1666.irrational a)/evalQPoly rf1666.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1666,rf1666]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (181/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-8019/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (79/476 : ℚ)*Polynomial.X^6 + Polynomial.C (-5044/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (563/3220 : ℚ)*Polynomial.X^8 + Polynomial.C (46871/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (-64951/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (30789/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (60863/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (332391/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (-333651/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (20389/5474 : ℚ)*Polynomial.X^15 + Polynomial.C (64881/54740 : ℚ)*Polynomial.X^16 + Polynomial.C (-41/34 : ℚ)*Polynomial.X^17
theorem eval1 (a : ℝ) (h : rf1690.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1690.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1690.rational a+Real.sqrt 2*evalQPoly rf1690.irrational a)/evalQPoly rf1690.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1690,rf1666]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (3/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-164/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (5779/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-65043/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (1187/340 : ℚ)*Polynomial.X^8 + Polynomial.C (-72784/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (134187/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (40875/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-10903/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-14036/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (384/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (115911/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (447/644 : ℚ)*Polynomial.X^16
theorem eval2 (a : ℝ) (h : rf1736.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1736.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1736.rational a+Real.sqrt 2*evalQPoly rf1736.irrational a)/evalQPoly rf1736.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1736,rf1666]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-33/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (81/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-5293/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (66/391 : ℚ)*Polynomial.X^12 + Polynomial.C (19699/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-17601/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (25/92 : ℚ)*Polynomial.X^15
theorem eval3 (a : ℝ) (h : rf1805.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1805.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1805.rational a+Real.sqrt 2*evalQPoly rf1805.irrational a)/evalQPoly rf1805.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1805,rf1666]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/238 : ℚ)*Polynomial.X^4 + Polynomial.C (809/4760 : ℚ)*Polynomial.X^5 + Polynomial.C (-23853/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (131847/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-93287/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (17557/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (115911/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-30542/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-305103/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (2396777/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-470627/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (361803/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (-2439/3910 : ℚ)*Polynomial.X^16 + Polynomial.C (-66131/21896 : ℚ)*Polynomial.X^17
theorem eval4 (a : ℝ) (h : rf1712.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1712.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1712.rational a+Real.sqrt 2*evalQPoly rf1712.irrational a)/evalQPoly rf1712.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1712,rf1666]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-167/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (7943/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-9869/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (26793/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-33293/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-91543/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (73999/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-40237/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (17023/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-296347/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (87063/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-759923/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (32801/3220 : ℚ)*Polynomial.X^15 + Polynomial.C (-4383/1564 : ℚ)*Polynomial.X^16
theorem eval5 (a : ℝ) (h : rf1759.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1759.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1759.rational a+Real.sqrt 2*evalQPoly rf1759.irrational a)/evalQPoly rf1759.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1759,rf1666]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (19/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (183/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-538/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (27621/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-73091/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (1324/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-12983/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-58334/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (172371/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (1021/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (51007/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-102007/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (209/161 : ℚ)*Polynomial.X^15
theorem eval6 (a : ℝ) (h : rf1827.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1827.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1827.rational a+Real.sqrt 2*evalQPoly rf1827.irrational a)/evalQPoly rf1827.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1827,rf1666]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (93/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (569/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-113/1288 : ℚ)*Polynomial.X^5 + Polynomial.C (58087/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-209037/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (69281/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (-675489/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (335331/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (543579/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-1082593/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (886469/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-172075/21896 : ℚ)*Polynomial.X^14 + Polynomial.C (777781/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (2477/21896 : ℚ)*Polynomial.X^16
theorem eval7 (a : ℝ) (h : rf1781.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1781.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1781.rational a+Real.sqrt 2*evalQPoly rf1781.irrational a)/evalQPoly rf1781.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1781,rf1666]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (3/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (93/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1597/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (263/1190 : ℚ)*Polynomial.X^6 + Polynomial.C (-167/391 : ℚ)*Polynomial.X^7 + Polynomial.C (4057/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (8941/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-66407/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (36531/15640 : ℚ)*Polynomial.X^11 + Polynomial.C (-11232/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (77919/7820 : ℚ)*Polynomial.X^13 + Polynomial.C (-16733/1955 : ℚ)*Polynomial.X^14 + Polynomial.C (4333/1564 : ℚ)*Polynomial.X^15
theorem eval8 (a : ℝ) (h : rf1850.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1850.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1850.rational a+Real.sqrt 2*evalQPoly rf1850.irrational a)/evalQPoly rf1850.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1850,rf1666]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (19/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-201/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (9893/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-6461/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (26024/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-26848/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2071/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (48941/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (31887/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-62651/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (179427/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-1521/644 : ℚ)*Polynomial.X^14
theorem eval9 (a : ℝ) (h : rf1896.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1896.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1896.rational a+Real.sqrt 2*evalQPoly rf1896.irrational a)/evalQPoly rf1896.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1896,rf1666]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (43/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-929/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (86/805 : ℚ)*Polynomial.X^6 + Polynomial.C (26227/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-4602/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (6915/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (61961/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-48471/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-19813/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (315349/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-32204/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (4127/1564 : ℚ)*Polynomial.X^15
theorem eval10 (a : ℝ) (h : rf1872.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1872.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1872.rational a+Real.sqrt 2*evalQPoly rf1872.irrational a)/evalQPoly rf1872.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1872,rf1666]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (3/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (94/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3251/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (433/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-19837/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-451/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (40249/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-175019/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (181521/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (32219/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-67203/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (100183/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-817/782 : ℚ)*Polynomial.X^14
theorem eval11 (a : ℝ) (h : rf1919.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1919.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1919.rational a+Real.sqrt 2*evalQPoly rf1919.irrational a)/evalQPoly rf1919.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1919,rf1666]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even074
