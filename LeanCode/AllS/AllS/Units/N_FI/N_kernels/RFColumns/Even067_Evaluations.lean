import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even067
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1659.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/31280 : ℚ)*Polynomial.X^2 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-1341/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-45/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (12587/31280 : ℚ)*Polynomial.X^6 + Polynomial.C (-192307/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (519081/31280 : ℚ)*Polynomial.X^8 + Polynomial.C (-5494459/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (22230147/218960 : ℚ)*Polynomial.X^10 + Polynomial.C (-1888244/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (27474457/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-8740279/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (509343/12880 : ℚ)*Polynomial.X^14 + Polynomial.C (-7149/1564 : ℚ)*Polynomial.X^15 + Polynomial.C (-4807611/218960 : ℚ)*Polynomial.X^16 + Polynomial.C (1299411/109480 : ℚ)*Polynomial.X^17 + Polynomial.C (24343/3910 : ℚ)*Polynomial.X^18
theorem eval0 (a : ℝ) (h : rf1659.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1659.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1659.rational a+Real.sqrt 2*evalQPoly rf1659.irrational a)/evalQPoly rf1659.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1659,rf1659]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/437920 : ℚ)*Polynomial.X^1 + Polynomial.C (1/31280 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/437920 : ℚ)*Polynomial.X^3 + Polynomial.C (-5/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (7059/437920 : ℚ)*Polynomial.X^5 + Polynomial.C (-14139/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (58381/437920 : ℚ)*Polynomial.X^7 + Polynomial.C (-7347/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-189751/437920 : ℚ)*Polynomial.X^9 + Polynomial.C (46039/31280 : ℚ)*Polynomial.X^10 + Polynomial.C (-941233/437920 : ℚ)*Polynomial.X^11 + Polynomial.C (9771/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (2118377/437920 : ℚ)*Polynomial.X^13 + Polynomial.C (-1490189/218960 : ℚ)*Polynomial.X^14 + Polynomial.C (559607/437920 : ℚ)*Polynomial.X^15 + Polynomial.C (10919/3128 : ℚ)*Polynomial.X^16 + Polynomial.C (-1281/680 : ℚ)*Polynomial.X^17
theorem eval1 (a : ℝ) (h : rf1683.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1683.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1683.rational a+Real.sqrt 2*evalQPoly rf1683.irrational a)/evalQPoly rf1683.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1683,rf1659]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-57/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (113/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (-19/2380 : ℚ)*Polynomial.X^5 + Polynomial.C (-2157/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (45443/15640 : ℚ)*Polynomial.X^7 + Polynomial.C (-1648263/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (1311203/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-313157/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (13167257/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-224971/3128 : ℚ)*Polynomial.X^12 + Polynomial.C (-123885/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (309177/7820 : ℚ)*Polynomial.X^14 + Polynomial.C (-941013/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (-1471/184 : ℚ)*Polynomial.X^16
theorem eval2 (a : ℝ) (h : rf1729.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1729.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1729.rational a+Real.sqrt 2*evalQPoly rf1729.irrational a)/evalQPoly rf1729.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1729,rf1659]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (249/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-21/782 : ℚ)*Polynomial.X^7 + Polynomial.C (521/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-2748/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (6217/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (265/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-66971/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (37206/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-175/68 : ℚ)*Polynomial.X^14 + Polynomial.C (203/230 : ℚ)*Polynomial.X^15
theorem eval3 (a : ℝ) (h : rf1798.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1798.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1798.rational a+Real.sqrt 2*evalQPoly rf1798.irrational a)/evalQPoly rf1798.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1798,rf1659]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/31280 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (1299/218960 : ℚ)*Polynomial.X^3 + Polynomial.C (177/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-87191/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (372661/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-492771/31280 : ℚ)*Polynomial.X^7 + Polynomial.C (359233/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-3718301/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (1355009/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (-1617407/218960 : ℚ)*Polynomial.X^11 + Polynomial.C (-809219/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (26462203/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (-2594441/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-661487/12880 : ℚ)*Polynomial.X^15 + Polynomial.C (318089/10948 : ℚ)*Polynomial.X^16 + Polynomial.C (73173/15640 : ℚ)*Polynomial.X^17
theorem eval4 (a : ℝ) (h : rf1705.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1705.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1705.rational a+Real.sqrt 2*evalQPoly rf1705.irrational a)/evalQPoly rf1705.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1705,rf1659]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/437920 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/31280 : ℚ)*Polynomial.X^1 + Polynomial.C (1/19040 : ℚ)*Polynomial.X^2 + Polynomial.C (13/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-6523/437920 : ℚ)*Polynomial.X^4 + Polynomial.C (13119/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-54969/437920 : ℚ)*Polynomial.X^6 + Polynomial.C (73/920 : ℚ)*Polynomial.X^7 + Polynomial.C (28771/87584 : ℚ)*Polynomial.X^8 + Polynomial.C (-292057/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (1298589/437920 : ℚ)*Polynomial.X^10 + Polynomial.C (-52378/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-172801/437920 : ℚ)*Polynomial.X^12 + Polynomial.C (368119/31280 : ℚ)*Polynomial.X^13 + Polynomial.C (-9144251/437920 : ℚ)*Polynomial.X^14 + Polynomial.C (252237/15640 : ℚ)*Polynomial.X^15 + Polynomial.C (-74347/15640 : ℚ)*Polynomial.X^16
theorem eval5 (a : ℝ) (h : rf1752.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1752.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1752.rational a+Real.sqrt 2*evalQPoly rf1752.irrational a)/evalQPoly rf1752.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1752,rf1659]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (27/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-7/1564 : ℚ)*Polynomial.X^3 + Polynomial.C (149/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (123/460 : ℚ)*Polynomial.X^5 + Polynomial.C (-976/391 : ℚ)*Polynomial.X^6 + Polynomial.C (93037/7820 : ℚ)*Polynomial.X^7 + Polynomial.C (-952423/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (3497401/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-533211/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (9409/340 : ℚ)*Polynomial.X^11 + Polynomial.C (1127641/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-291121/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (152961/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (991/460 : ℚ)*Polynomial.X^15
theorem eval6 (a : ℝ) (h : rf1820.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1820.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1820.rational a+Real.sqrt 2*evalQPoly rf1820.irrational a)/evalQPoly rf1820.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1820,rf1659]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (9/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-159/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-33/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (1617/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (-181201/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (424001/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-29979/1190 : ℚ)*Polynomial.X^8 + Polynomial.C (3300469/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-2306161/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (6747483/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-3960111/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1054443/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (6266073/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-1115069/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (-15996/1955 : ℚ)*Polynomial.X^16
theorem eval7 (a : ℝ) (h : rf1774.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1774.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1774.rational a+Real.sqrt 2*evalQPoly rf1774.irrational a)/evalQPoly rf1774.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1774,rf1659]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (263/12880 : ℚ)*Polynomial.X^5 + Polynomial.C (-1321/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (293/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (-109/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (111981/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (-87337/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (31861/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (141849/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-328773/31280 : ℚ)*Polynomial.X^13 + Polynomial.C (15956/1955 : ℚ)*Polynomial.X^14 + Polynomial.C (-18137/7820 : ℚ)*Polynomial.X^15
theorem eval8 (a : ℝ) (h : rf1843.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1843.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1843.rational a+Real.sqrt 2*evalQPoly rf1843.irrational a)/evalQPoly rf1843.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1843,rf1659]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^2 + Polynomial.C (19/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (649/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-24931/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (8061/2380 : ℚ)*Polynomial.X^6 + Polynomial.C (-377887/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (948663/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-42396/805 : ℚ)*Polynomial.X^9 + Polynomial.C (553467/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (33291/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-36589/1564 : ℚ)*Polynomial.X^12 + Polynomial.C (437441/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (461/92 : ℚ)*Polynomial.X^14
theorem eval9 (a : ℝ) (h : rf1889.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1889.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1889.rational a+Real.sqrt 2*evalQPoly rf1889.irrational a)/evalQPoly rf1889.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1889,rf1659]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (7/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-61/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1653/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (53787/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-2115/782 : ℚ)*Polynomial.X^6 + Polynomial.C (205117/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-217541/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-1421807/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (128267/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-39537/595 : ℚ)*Polynomial.X^11 + Polynomial.C (198531/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (3249529/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-46111/2737 : ℚ)*Polynomial.X^14 + Polynomial.C (-24699/3910 : ℚ)*Polynomial.X^15
theorem eval10 (a : ℝ) (h : rf1865.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1865.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1865.rational a+Real.sqrt 2*evalQPoly rf1865.irrational a)/evalQPoly rf1865.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1865,rf1659]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (4999/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-151/2380 : ℚ)*Polynomial.X^5 + Polynomial.C (377/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (13/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-138867/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (56153/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-48719/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-59249/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (1055277/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-42709/7820 : ℚ)*Polynomial.X^13 + Polynomial.C (15897/7820 : ℚ)*Polynomial.X^14
theorem eval11 (a : ℝ) (h : rf1912.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1912.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1912.rational a+Real.sqrt 2*evalQPoly rf1912.irrational a)/evalQPoly rf1912.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1912,rf1659]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even067
