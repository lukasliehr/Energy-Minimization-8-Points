import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even059
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1651.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1288 : ℚ)*Polynomial.X^2 + Polynomial.C (1/170 : ℚ)*Polynomial.X^3 + Polynomial.C (-781/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-888/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (76569/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-89781/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (268649/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-96395/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (1069021/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (995447/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-1145281/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (1648567/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-5526177/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-38973/3910 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1651.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1651.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1651.rational a+Real.sqrt 2*evalQPoly rf1651.irrational a)/evalQPoly rf1651.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1651,rf1651]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (59/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-2347/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (8593/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-185037/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (119597/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-288161/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-620343/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (719017/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (-3407/68 : ℚ)*Polynomial.X^11 + Polynomial.C (261775/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (326909/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (-17479/680 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1675.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1675.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1675.rational a+Real.sqrt 2*evalQPoly rf1675.irrational a)/evalQPoly rf1675.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1675,rf1651]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (19/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/680 : ℚ)*Polynomial.X^4 + Polynomial.C (1759/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-68823/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (16119/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-744689/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-64371/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (341123/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-272807/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (4003913/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-203/23 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1721.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1721.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1721.rational a+Real.sqrt 2*evalQPoly rf1721.irrational a)/evalQPoly rf1721.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1721,rf1651]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-18/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-343/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (650/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-13154/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (4017/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-173163/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-111847/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (188327/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-35091/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (9723/920 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1790.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1790.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1790.rational a+Real.sqrt 2*evalQPoly rf1790.irrational a)/evalQPoly rf1790.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1790,rf1651]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (1/340 : ℚ)*Polynomial.X^3 + Polynomial.C (-113/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (537/1190 : ℚ)*Polynomial.X^5 + Polynomial.C (-209721/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (116033/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-20597/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-968741/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1083097/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (-3040339/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (41716/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (169982/2737 : ℚ)*Polynomial.X^13 + Polynomial.C (-854613/15640 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1697.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1697.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1697.rational a+Real.sqrt 2*evalQPoly rf1697.irrational a)/evalQPoly rf1697.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1697,rf1651]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (5/1564 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/595 : ℚ)*Polynomial.X^3 + Polynomial.C (-819/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (36399/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-91269/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (1148/115 : ℚ)*Polynomial.X^7 + Polynomial.C (-260583/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (10973/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (2900171/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-1736694/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (2162243/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (-519309/7820 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1744.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1744.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1744.rational a+Real.sqrt 2*evalQPoly rf1744.irrational a)/evalQPoly rf1744.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1744,rf1651]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (727/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-297/4760 : ℚ)*Polynomial.X^4 + Polynomial.C (341/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (6539/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-2845/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-277677/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (87145/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-127814/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (2095/644 : ℚ)*Polynomial.X^11 + Polynomial.C (1853/920 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1812.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1812.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1812.rational a+Real.sqrt 2*evalQPoly rf1812.irrational a)/evalQPoly rf1812.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1812,rf1651]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (61/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-571/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (1927/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (-3919/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (14403/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (273/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-355807/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (484751/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-30517/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (332501/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-857809/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (39969/7820 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1766.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1766.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1766.rational a+Real.sqrt 2*evalQPoly rf1766.irrational a)/evalQPoly rf1766.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1766,rf1651]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-121/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (11561/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-16757/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (26836/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-89819/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-14849/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (94171/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-28011/1190 : ℚ)*Polynomial.X^10 + Polynomial.C (154313/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-66451/15640 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1835.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1835.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1835.rational a+Real.sqrt 2*evalQPoly rf1835.irrational a)/evalQPoly rf1835.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1835,rf1651]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (319/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-177/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (587/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (209/391 : ℚ)*Polynomial.X^6 + Polynomial.C (-18409/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (27099/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-9616/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (56072/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-38/23 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1881.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1881.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1881.rational a+Real.sqrt 2*evalQPoly rf1881.irrational a)/evalQPoly rf1881.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1881,rf1651]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-1079/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (14591/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-1699/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (9599/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (6841/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-71397/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (30307/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (-35192/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-816619/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (277971/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1857.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1857.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1857.rational a+Real.sqrt 2*evalQPoly rf1857.irrational a)/evalQPoly rf1857.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1857,rf1651]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (13/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/1564 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/595 : ℚ)*Polynomial.X^3 + Polynomial.C (37/322 : ℚ)*Polynomial.X^4 + Polynomial.C (-9113/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (8149/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-45046/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-53441/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (375813/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-36749/1564 : ℚ)*Polynomial.X^10 + Polynomial.C (32347/1955 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1904.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1904.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1904.rational a+Real.sqrt 2*evalQPoly rf1904.irrational a)/evalQPoly rf1904.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1904,rf1651]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even059
