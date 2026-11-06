import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even049
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1320.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-29/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-228/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (30511/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-87583/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (28039/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-19466/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (37561/3128 : ℚ)*Polynomial.X^10 + Polynomial.C (-526817/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (324703/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (5822/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-24317/3128 : ℚ)*Polynomial.X^14 + Polynomial.C (173379/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (7113/1955 : ℚ)*Polynomial.X^16 + Polynomial.C (2180/2737 : ℚ)*Polynomial.X^17
theorem eval0 (a : ℝ) (h : rf1320.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1320.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1320.rational a+Real.sqrt 2*evalQPoly rf1320.irrational a)/evalQPoly rf1320.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1320,rf1320]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (6367/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-11457/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (2228/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (93/1190 : ℚ)*Polynomial.X^8 + Polynomial.C (-24101/31280 : ℚ)*Polynomial.X^9 + Polynomial.C (19387/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (-31659/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-29041/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (31617/43792 : ℚ)*Polynomial.X^13 + Polynomial.C (-55763/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (1370/2737 : ℚ)*Polynomial.X^15 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^16
theorem eval1 (a : ℝ) (h : rf1339.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1339.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1339.rational a+Real.sqrt 2*evalQPoly rf1339.irrational a)/evalQPoly rf1339.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1339,rf1320]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/2380 : ℚ)*Polynomial.X^3 + Polynomial.C (38/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (491/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-2595/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (42253/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-3148/595 : ℚ)*Polynomial.X^8 + Polynomial.C (278447/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-72803/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-25099/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (88838/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-14713/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-1801/644 : ℚ)*Polynomial.X^14 + Polynomial.C (-170/161 : ℚ)*Polynomial.X^15
theorem eval2 (a : ℝ) (h : rf1375.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1375.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1375.rational a+Real.sqrt 2*evalQPoly rf1375.irrational a)/evalQPoly rf1375.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1375,rf1320]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-33/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (81/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-5293/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (66/391 : ℚ)*Polynomial.X^11 + Polynomial.C (19699/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-17601/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (25/92 : ℚ)*Polynomial.X^14
theorem eval3 (a : ℝ) (h : rf1429.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1429.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1429.rational a+Real.sqrt 2*evalQPoly rf1429.irrational a)/evalQPoly rf1429.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1429,rf1320]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (129/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (957/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-1717/6440 : ℚ)*Polynomial.X^5 + Polynomial.C (80803/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-49587/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (215731/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-648199/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-89979/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (89443/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (65049/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1017783/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (50751/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (265711/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (3225/2737 : ℚ)*Polynomial.X^16
theorem eval4 (a : ℝ) (h : rf1356.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1356.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1356.rational a+Real.sqrt 2*evalQPoly rf1356.irrational a)/evalQPoly rf1356.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1356,rf1320]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (179/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-6523/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (13299/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-3369/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2647/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (230859/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (-55925/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (24657/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (133249/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-1156721/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (7535/3128 : ℚ)*Polynomial.X^13 + Polynomial.C (4423/3910 : ℚ)*Polynomial.X^14 + Polynomial.C (-1393/1564 : ℚ)*Polynomial.X^15
theorem eval5 (a : ℝ) (h : rf1393.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1393.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1393.rational a+Real.sqrt 2*evalQPoly rf1393.irrational a)/evalQPoly rf1393.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1393,rf1320]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-57/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-93/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (1641/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (-32517/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (48971/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-32467/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (238821/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (33353/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-6337/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (-181623/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (194317/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-113/161 : ℚ)*Polynomial.X^14
theorem eval6 (a : ℝ) (h : rf1446.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1446.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1446.rational a+Real.sqrt 2*evalQPoly rf1446.irrational a)/evalQPoly rf1446.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1446,rf1320]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (19/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-164/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1949/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-53317/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (23997/7820 : ℚ)*Polynomial.X^7 + Polynomial.C (-83962/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (426873/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-8237/1564 : ℚ)*Polynomial.X^10 + Polynomial.C (-21673/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (22942/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (3355/644 : ℚ)*Polynomial.X^13 + Polynomial.C (-50017/7820 : ℚ)*Polynomial.X^14 + Polynomial.C (-12527/10948 : ℚ)*Polynomial.X^15
theorem eval7 (a : ℝ) (h : rf1410.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1410.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1410.rational a+Real.sqrt 2*evalQPoly rf1410.irrational a)/evalQPoly rf1410.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1410,rf1320]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-94/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2561/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-7373/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (4391/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (1299/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-234597/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (5630/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (266191/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-106849/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (27303/3910 : ℚ)*Polynomial.X^13 + Polynomial.C (-3395/1564 : ℚ)*Polynomial.X^14
theorem eval8 (a : ℝ) (h : rf1464.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1464.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1464.rational a+Real.sqrt 2*evalQPoly rf1464.irrational a)/evalQPoly rf1464.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1464,rf1320]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (11/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (79/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-9887/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (23013/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-54603/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (3526/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-2501/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-841/230 : ℚ)*Polynomial.X^10 + Polynomial.C (24641/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (1789/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (447/322 : ℚ)*Polynomial.X^13
theorem eval9 (a : ℝ) (h : rf1500.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1500.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1500.rational a+Real.sqrt 2*evalQPoly rf1500.irrational a)/evalQPoly rf1500.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1500,rf1320]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1564 : ℚ)*Polynomial.X^3 + Polynomial.C (-1703/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (2661/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-9888/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1647/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (73897/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-140/23 : ℚ)*Polynomial.X^9 + Polynomial.C (5069/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (383681/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-231579/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-69911/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-1559/782 : ℚ)*Polynomial.X^14
theorem eval10 (a : ℝ) (h : rf1481.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1481.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1481.rational a+Real.sqrt 2*evalQPoly rf1481.irrational a)/evalQPoly rf1481.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1481,rf1320]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-373/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (2503/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-3533/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (1075/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (9477/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-12891/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (773/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (13043/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (44003/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-29306/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (793/782 : ℚ)*Polynomial.X^13
theorem eval11 (a : ℝ) (h : rf1518.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1518.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1518.rational a+Real.sqrt 2*evalQPoly rf1518.irrational a)/evalQPoly rf1518.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1518,rf1320]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even049
