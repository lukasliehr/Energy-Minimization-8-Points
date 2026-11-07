import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even079
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1671.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (83/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-321/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-443/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (79053/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-35883/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (420323/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (7207/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-460485/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (79493/2380 : ℚ)*Polynomial.X^12 + Polynomial.C (-17057/952 : ℚ)*Polynomial.X^13 + Polynomial.C (-239993/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (527633/15640 : ℚ)*Polynomial.X^15 + Polynomial.C (-407317/27370 : ℚ)*Polynomial.X^16 + Polynomial.C (-351919/109480 : ℚ)*Polynomial.X^17 + Polynomial.C (205633/54740 : ℚ)*Polynomial.X^18
theorem eval0 (a : ℝ) (h : rf1671.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1671.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1671.rational a+Real.sqrt 2*evalQPoly rf1671.irrational a)/evalQPoly rf1671.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1671,rf1671]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-81/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (4579/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-13301/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (44571/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-176021/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (141/56 : ℚ)*Polynomial.X^9 + Polynomial.C (280269/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-440101/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (1802599/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-12362/391 : ℚ)*Polynomial.X^13 + Polynomial.C (226679/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (-15541/10948 : ℚ)*Polynomial.X^15 + Polynomial.C (-183283/54740 : ℚ)*Polynomial.X^16 + Polynomial.C (229/170 : ℚ)*Polynomial.X^17
theorem eval1 (a : ℝ) (h : rf1695.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1695.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1695.rational a+Real.sqrt 2*evalQPoly rf1695.irrational a)/evalQPoly rf1695.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1695,rf1671]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1/4760 : ℚ)*Polynomial.X^4 + Polynomial.C (239/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-7167/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (2339/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-9069/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-2004/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-86413/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (29093/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (93053/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-29755/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (82191/21896 : ℚ)*Polynomial.X^14 + Polynomial.C (38/595 : ℚ)*Polynomial.X^15 + Polynomial.C (-1355/1288 : ℚ)*Polynomial.X^16
theorem eval2 (a : ℝ) (h : rf1741.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1741.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1741.rational a+Real.sqrt 2*evalQPoly rf1741.irrational a)/evalQPoly rf1741.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1741,rf1671]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (0 : ℚ)*Polynomial.X^5 + Polynomial.C (0 : ℚ)*Polynomial.X^6 + Polynomial.C (0 : ℚ)*Polynomial.X^7 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2/805 : ℚ)*Polynomial.X^9 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-402/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-106/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (1514/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-1882/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (6/115 : ℚ)*Polynomial.X^15
theorem eval3 (a : ℝ) (h : rf1810.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1810.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1810.rational a+Real.sqrt 2*evalQPoly rf1810.irrational a)/evalQPoly rf1810.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1810,rf1671]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/21896 : ℚ)*Polynomial.X^3 + Polynomial.C (13/3220 : ℚ)*Polynomial.X^4 + Polynomial.C (9077/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-22201/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (368349/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-386877/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (13525/3128 : ℚ)*Polynomial.X^9 + Polynomial.C (444457/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-5557271/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (3760731/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-4562373/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-422827/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (1152887/21896 : ℚ)*Polynomial.X^15 + Polynomial.C (-2212491/54740 : ℚ)*Polynomial.X^16 + Polynomial.C (1314769/109480 : ℚ)*Polynomial.X^17
theorem eval4 (a : ℝ) (h : rf1717.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1717.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1717.rational a+Real.sqrt 2*evalQPoly rf1717.irrational a)/evalQPoly rf1717.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1717,rf1671]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/1288 : ℚ)*Polynomial.X^2 + Polynomial.C (131/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-97/1190 : ℚ)*Polynomial.X^4 + Polynomial.C (1993/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-52737/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (65236/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-22319/3128 : ℚ)*Polynomial.X^8 + Polynomial.C (26935/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (389961/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (-1458113/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (4658159/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1190292/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (3053833/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (-1699/85 : ℚ)*Polynomial.X^15 + Polynomial.C (23051/7820 : ℚ)*Polynomial.X^16
theorem eval5 (a : ℝ) (h : rf1764.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1764.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1764.rational a+Real.sqrt 2*evalQPoly rf1764.irrational a)/evalQPoly rf1764.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1764,rf1671]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (-7/782 : ℚ)*Polynomial.X^4 + Polynomial.C (1067/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-3011/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-3407/15640 : ℚ)*Polynomial.X^7 + Polynomial.C (4733/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (21571/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (-12991/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (244221/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (140283/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-1203499/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (476779/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (-16299/6440 : ℚ)*Polynomial.X^15
theorem eval6 (a : ℝ) (h : rf1832.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1832.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1832.rational a+Real.sqrt 2*evalQPoly rf1832.irrational a)/evalQPoly rf1832.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1832,rf1671]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-83/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-53/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (1779/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-28131/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (209733/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-45191/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (346933/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (417939/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-574221/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (1995617/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-2530547/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-40373/10948 : ℚ)*Polynomial.X^14 + Polynomial.C (1414479/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (-312037/54740 : ℚ)*Polynomial.X^16
theorem eval7 (a : ℝ) (h : rf1786.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1786.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1786.rational a+Real.sqrt 2*evalQPoly rf1786.irrational a)/evalQPoly rf1786.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1786,rf1671]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-67/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-31/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (4241/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-46479/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (21271/7820 : ℚ)*Polynomial.X^7 + Polynomial.C (-4181/805 : ℚ)*Polynomial.X^8 + Polynomial.C (211867/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (483039/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-1838537/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (21076/391 : ℚ)*Polynomial.X^12 + Polynomial.C (-680613/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (200089/7820 : ℚ)*Polynomial.X^14 + Polynomial.C (-44443/7820 : ℚ)*Polynomial.X^15
theorem eval8 (a : ℝ) (h : rf1855.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1855.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1855.rational a+Real.sqrt 2*evalQPoly rf1855.irrational a)/evalQPoly rf1855.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1855,rf1671]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (229/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-6343/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (16433/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-389/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-7839/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (14241/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-161593/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (5884/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (13082/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (-449809/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (2187/644 : ℚ)*Polynomial.X^14
theorem eval9 (a : ℝ) (h : rf1901.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1901.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1901.rational a+Real.sqrt 2*evalQPoly rf1901.irrational a)/evalQPoly rf1901.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1901,rf1671]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (313/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (213/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-24963/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (4223/3220 : ℚ)*Polynomial.X^6 + Polynomial.C (-355423/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (24399/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (145893/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (-1337621/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (2625379/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (70957/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-514519/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (1694841/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (-161979/15640 : ℚ)*Polynomial.X^15
theorem eval10 (a : ℝ) (h : rf1877.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1877.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1877.rational a+Real.sqrt 2*evalQPoly rf1877.irrational a)/evalQPoly rf1877.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1877,rf1671]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/161 : ℚ)*Polynomial.X^3 + Polynomial.C (785/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-418/595 : ℚ)*Polynomial.X^5 + Polynomial.C (10411/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-6635/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-78053/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (153469/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-542723/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (239261/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-12913/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (-8943/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (3559/3910 : ℚ)*Polynomial.X^14
theorem eval11 (a : ℝ) (h : rf1924.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1924.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1924.rational a+Real.sqrt 2*evalQPoly rf1924.irrational a)/evalQPoly rf1924.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1924,rf1671]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even079
