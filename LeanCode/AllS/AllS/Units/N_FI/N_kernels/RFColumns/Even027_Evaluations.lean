import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even027
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1058.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (167/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-1949/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (398/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-7911/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (3073/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (-96253/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (428271/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-8529/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-587941/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (572839/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (81653/27370 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf1058.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1058.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1058.rational a+Real.sqrt 2*evalQPoly rf1058.irrational a)/evalQPoly rf1058.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1058,rf1058]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (19/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-18/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (307/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (11/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-5521/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (1177/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (28316/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-9938/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-14333/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (594/85 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf1073.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1073.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1073.rational a+Real.sqrt 2*evalQPoly rf1073.irrational a)/evalQPoly rf1073.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1073,rf1058]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-143/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (907/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-10303/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (14482/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-6723/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (431/391 : ℚ)*Polynomial.X^8 + Polynomial.C (113083/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-107267/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (533/644 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf1101.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1101.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1101.rational a+Real.sqrt 2*evalQPoly rf1101.irrational a)/evalQPoly rf1101.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1101,rf1058]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (41/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (73/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^5 + Polynomial.C (1077/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-1291/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-10273/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (58516/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-528/115 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1143.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1143.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1143.rational a+Real.sqrt 2*evalQPoly rf1143.irrational a)/evalQPoly rf1143.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1143,rf1058]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (1033/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-8193/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (1879/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-1390/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-16211/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1657/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (24669/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (-4971/391 : ℚ)*Polynomial.X^10 + Polynomial.C (-68163/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (690569/54740 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf1086.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1086.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1086.rational a+Real.sqrt 2*evalQPoly rf1086.irrational a)/evalQPoly rf1086.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1086,rf1058]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (701/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-2837/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (11149/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-32751/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (1013/391 : ℚ)*Polynomial.X^8 + Polynomial.C (15437/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-53341/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (33608/1955 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf1115.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1115.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1115.rational a+Real.sqrt 2*evalQPoly rf1115.irrational a)/evalQPoly rf1115.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1115,rf1058]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-636/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (7873/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-9523/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (539/782 : ℚ)*Polynomial.X^6 + Polynomial.C (-4656/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (12129/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (4559/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-6539/3220 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf1156.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1156.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1156.rational a+Real.sqrt 2*evalQPoly rf1156.irrational a)/evalQPoly rf1156.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1156,rf1058]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^1 + Polynomial.C (13/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (326/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/595 : ℚ)*Polynomial.X^4 + Polynomial.C (5162/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-513/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-22804/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (37497/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-133323/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (109729/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-6666/13685 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf1128.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1128.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1128.rational a+Real.sqrt 2*evalQPoly rf1128.irrational a)/evalQPoly rf1128.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1128,rf1058]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (117/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-65/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (1287/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-6563/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1971/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (20721/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-7716/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (2086/1955 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf1170.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1170.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1170.rational a+Real.sqrt 2*evalQPoly rf1170.irrational a)/evalQPoly rf1170.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1170,rf1058]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (5/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-733/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (2999/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-372/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-4045/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (41533/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-30146/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (211/322 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf1198.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1198.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1198.rational a+Real.sqrt 2*evalQPoly rf1198.irrational a)/evalQPoly rf1198.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1198,rf1058]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (142/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-235/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (47/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (737/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-638/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (49101/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (6649/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-27189/7820 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf1183.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1183.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1183.rational a+Real.sqrt 2*evalQPoly rf1183.irrational a)/evalQPoly rf1183.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1183,rf1058]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (29/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-541/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1401/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-5839/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (9419/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (23673/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-8131/1955 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf1212.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1212.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1212.rational a+Real.sqrt 2*evalQPoly rf1212.irrational a)/evalQPoly rf1212.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1212,rf1058]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even027
