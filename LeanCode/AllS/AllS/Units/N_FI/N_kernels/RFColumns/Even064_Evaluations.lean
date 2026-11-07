import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even064
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1656.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (87/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-15/782 : ℚ)*Polynomial.X^4 + Polynomial.C (9423/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-25643/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (50789/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-12496/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (1642429/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-3239553/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (1555021/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (8503/782 : ℚ)*Polynomial.X^12 + Polynomial.C (-1213935/21896 : ℚ)*Polynomial.X^13 + Polynomial.C (3660103/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (140059/10948 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1656.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1656.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1656.rational a+Real.sqrt 2*evalQPoly rf1656.irrational a)/evalQPoly rf1656.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1656,rf1656]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (19/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (471/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-81/1190 : ℚ)*Polynomial.X^5 + Polynomial.C (827/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-24279/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (6928/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-1043/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-379087/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (385653/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-72409/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-382059/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (409/17 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1680.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1680.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1680.rational a+Real.sqrt 2*evalQPoly rf1680.irrational a)/evalQPoly rf1680.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1680,rf1656]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (551/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1697/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (17427/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-49821/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (4373/595 : ℚ)*Polynomial.X^8 + Polynomial.C (-9777/1190 : ℚ)*Polynomial.X^9 + Polynomial.C (-9704/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (205092/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-205678/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (503/322 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1726.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1726.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1726.rational a+Real.sqrt 2*evalQPoly rf1726.irrational a)/evalQPoly rf1726.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1726,rf1656]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (13/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (97/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-206/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (1529/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-24882/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (38867/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (29611/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-23151/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (552763/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-320/23 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1795.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1795.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1795.rational a+Real.sqrt 2*evalQPoly rf1795.irrational a)/evalQPoly rf1795.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1795,rf1656]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (1/4760 : ℚ)*Polynomial.X^2 + Polynomial.C (537/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-1323/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (16019/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-39611/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-7087/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-68529/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (60343/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-559953/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (27191/476 : ℚ)*Polynomial.X^11 + Polynomial.C (-3803203/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-1682209/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (1095167/21896 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1702.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1702.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1702.rational a+Real.sqrt 2*evalQPoly rf1702.irrational a)/evalQPoly rf1702.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1702,rf1656]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-109/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (393/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-2344/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (2706/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-57102/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (20303/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-143317/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-449611/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (114137/1610 : ℚ)*Polynomial.X^11 + Polynomial.C (-1382314/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (23631/391 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1749.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1749.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1749.rational a+Real.sqrt 2*evalQPoly rf1749.irrational a)/evalQPoly rf1749.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1749,rf1656]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1753/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (11139/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-1889/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (33/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1303/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (11103/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-41999/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (139267/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-32981/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-3809/644 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1817.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1817.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1817.rational a+Real.sqrt 2*evalQPoly rf1817.irrational a)/evalQPoly rf1817.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1817,rf1656]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-47/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (12/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (107/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-3445/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (56657/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-10769/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-5484/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (662049/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-2087517/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (482193/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-205915/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (89987/4760 : ℚ)*Polynomial.X^12 + Polynomial.C (-131105/21896 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1771.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1771.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1771.rational a+Real.sqrt 2*evalQPoly rf1771.irrational a)/evalQPoly rf1771.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1771,rf1656]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (113/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-52/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (116/805 : ℚ)*Polynomial.X^5 + Polynomial.C (-11267/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (31268/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-29213/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-110513/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (41840/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-72007/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (2079/391 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1840.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1840.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1840.rational a+Real.sqrt 2*evalQPoly rf1840.irrational a)/evalQPoly rf1840.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1840,rf1656]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (43/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-2491/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (423/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (-10739/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-5479/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (130483/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-470123/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (555963/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-489129/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (2817/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1886.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1886.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1886.rational a+Real.sqrt 2*evalQPoly rf1886.irrational a)/evalQPoly rf1886.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1886,rf1656]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (739/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-225/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (845/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (1237/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-14561/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (72129/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-165187/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (124149/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (85667/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-12101/782 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1862.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1862.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1862.rational a+Real.sqrt 2*evalQPoly rf1862.irrational a)/evalQPoly rf1862.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1862,rf1656]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (113/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-407/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2869/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-2768/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (31582/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-12281/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-84461/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (409033/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-11295/782 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1909.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1909.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1909.rational a+Real.sqrt 2*evalQPoly rf1909.irrational a)/evalQPoly rf1909.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1909,rf1656]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even064
