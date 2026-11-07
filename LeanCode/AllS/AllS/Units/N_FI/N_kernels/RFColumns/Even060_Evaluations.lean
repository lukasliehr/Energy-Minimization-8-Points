import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even060
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1652.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (19/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-79/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (356/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2349/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-60883/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (570371/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-1412731/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (2332061/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-20273891/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (1522123/6440 : ℚ)*Polynomial.X^10 + Polynomial.C (-2579713/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-10577709/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (1446549/4760 : ℚ)*Polynomial.X^13 + Polynomial.C (-10900147/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-750615/10948 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1652.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1652.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1652.rational a+Real.sqrt 2*evalQPoly rf1652.irrational a)/evalQPoly rf1652.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1652,rf1652]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (148/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-267/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2918/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (53877/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-119072/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (309352/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-367653/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-776523/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (2213674/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-199733/805 : ℚ)*Polynomial.X^11 + Polynomial.C (263862/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (355395/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (-1654/17 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1676.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1676.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1676.rational a+Real.sqrt 2*evalQPoly rf1676.irrational a)/evalQPoly rf1676.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1676,rf1652]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (403/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-55/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-18483/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (7844/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-352841/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (1043549/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1026581/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (683673/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-1994177/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-2190663/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (2965317/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-3643/322 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1722.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1722.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1722.rational a+Real.sqrt 2*evalQPoly rf1722.irrational a)/evalQPoly rf1722.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1722,rf1652]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (6/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-86/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1859/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (11092/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-46792/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (107676/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-201759/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-5374/391 : ℚ)*Polynomial.X^9 + Polynomial.C (727956/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-11470/161 : ℚ)*Polynomial.X^11 + Polynomial.C (1921/46 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1791.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1791.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1791.rational a+Real.sqrt 2*evalQPoly rf1791.irrational a)/evalQPoly rf1791.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1791,rf1652]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (31/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-93/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (93/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (11817/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-55897/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (614531/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-334088/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (9152631/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-11180579/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (34889709/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-677401/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-1486393/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (18356477/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-5403347/21896 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1698.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1698.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1698.rational a+Real.sqrt 2*evalQPoly rf1698.irrational a)/evalQPoly rf1698.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1698,rf1652]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^1 + Polynomial.C (179/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-521/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1423/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (43/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-29936/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (622904/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-119033/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (226187/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (147867/595 : ℚ)*Polynomial.X^10 + Polynomial.C (-1547507/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (2314869/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-213955/782 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1745.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1745.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1745.rational a+Real.sqrt 2*evalQPoly rf1745.irrational a)/evalQPoly rf1745.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1745,rf1652]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (71/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (1431/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-26959/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (30637/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-118959/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (427883/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-4458667/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (160311/1190 : ℚ)*Polynomial.X^9 + Polynomial.C (-212857/1610 : ℚ)*Polynomial.X^10 + Polynomial.C (100147/1610 : ℚ)*Polynomial.X^11 + Polynomial.C (-1445/644 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1813.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1813.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1813.rational a+Real.sqrt 2*evalQPoly rf1813.irrational a)/evalQPoly rf1813.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1813,rf1652]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/6440 : ℚ)*Polynomial.X^1 + Polynomial.C (19/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-879/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (2419/6440 : ℚ)*Polynomial.X^4 + Polynomial.C (-46149/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-96651/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (634063/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1704121/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (18312583/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-2635273/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (12816973/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-3136359/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (1169673/21896 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1767.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1767.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1767.rational a+Real.sqrt 2*evalQPoly rf1767.irrational a)/evalQPoly rf1767.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1767,rf1652]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (29/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-164/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (33/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-38204/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (123392/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-201622/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-55737/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (109897/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-284439/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (162646/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (-13769/782 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1836.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1836.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1836.rational a+Real.sqrt 2*evalQPoly rf1836.irrational a)/evalQPoly rf1836.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1836,rf1652]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (41/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-701/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (4989/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-2301/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-9173/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (392963/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-163853/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (594317/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-142017/1564 : ℚ)*Polynomial.X^9 + Polynomial.C (3606487/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-14411/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1882.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1882.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1882.rational a+Real.sqrt 2*evalQPoly rf1882.irrational a)/evalQPoly rf1882.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1882,rf1652]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (78/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-285/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (2031/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (5087/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-50892/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (160127/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-50250/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-54361/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (191374/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-3515597/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (37129/391 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1858.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1858.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1858.rational a+Real.sqrt 2*evalQPoly rf1858.irrational a)/evalQPoly rf1858.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1858,rf1652]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (27/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-181/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-169/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (7388/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-8460/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (129972/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-28028/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-3701/595 : ℚ)*Polynomial.X^8 + Polynomial.C (173093/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-279595/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (26631/391 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1905.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1905.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1905.rational a+Real.sqrt 2*evalQPoly rf1905.irrational a)/evalQPoly rf1905.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1905,rf1652]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even060
