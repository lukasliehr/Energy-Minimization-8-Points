import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even058
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1650.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/437920 : ℚ)*Polynomial.X^2 + Polynomial.C (-39/31280 : ℚ)*Polynomial.X^3 + Polynomial.C (657/31280 : ℚ)*Polynomial.X^4 + Polynomial.C (-281/2576 : ℚ)*Polynomial.X^5 + Polynomial.C (-9601/31280 : ℚ)*Polynomial.X^6 + Polynomial.C (1754603/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (-12751901/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (56764137/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (-8833137/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (3511999/1904 : ℚ)*Polynomial.X^11 + Polynomial.C (-6048505/1904 : ℚ)*Polynomial.X^12 + Polynomial.C (920766657/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (-961009657/218960 : ℚ)*Polynomial.X^14 + Polynomial.C (162393349/43792 : ℚ)*Polynomial.X^15 + Polynomial.C (-547987711/218960 : ℚ)*Polynomial.X^16 + Polynomial.C (1138955/952 : ℚ)*Polynomial.X^17 + Polynomial.C (-25625359/87584 : ℚ)*Polynomial.X^18
theorem eval0 (a : ℝ) (h : rf1650.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1650.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1650.rational a+Real.sqrt 2*evalQPoly rf1650.irrational a)/evalQPoly rf1650.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1650,rf1650]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/875840 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (541/437920 : ℚ)*Polynomial.X^3 + Polynomial.C (213/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-24187/437920 : ℚ)*Polynomial.X^5 + Polynomial.C (7983/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (-592883/437920 : ℚ)*Polynomial.X^7 + Polynomial.C (719331/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (-1082807/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (9755/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (5749983/437920 : ℚ)*Polynomial.X^11 + Polynomial.C (-1744881/43792 : ℚ)*Polynomial.X^12 + Polynomial.C (763193/12512 : ℚ)*Polynomial.X^13 + Polynomial.C (-5957601/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (10911031/437920 : ℚ)*Polynomial.X^15 + Polynomial.C (-534307/218960 : ℚ)*Polynomial.X^16 + Polynomial.C (-1545/1088 : ℚ)*Polynomial.X^17
theorem eval1 (a : ℝ) (h : rf1674.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1674.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1674.rational a+Real.sqrt 2*evalQPoly rf1674.irrational a)/evalQPoly rf1674.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1674,rf1650]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/218960 : ℚ)*Polynomial.X^2 + Polynomial.C (1/644 : ℚ)*Polynomial.X^3 + Polynomial.C (-3397/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (96/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (107903/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (-410427/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (493057/9520 : ℚ)*Polynomial.X^8 + Polynomial.C (-3187666/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1409091/1904 : ℚ)*Polynomial.X^10 + Polynomial.C (-93288513/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (623070801/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-77626/23 : ℚ)*Polynomial.X^13 + Polynomial.C (118574961/43792 : ℚ)*Polynomial.X^14 + Polynomial.C (-72463577/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (773289/2576 : ℚ)*Polynomial.X^16
theorem eval2 (a : ℝ) (h : rf1720.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1720.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1720.rational a+Real.sqrt 2*evalQPoly rf1720.irrational a)/evalQPoly rf1720.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1720,rf1650]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/218960 : ℚ)*Polynomial.X^3 + Polynomial.C (-121/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (355/43792 : ℚ)*Polynomial.X^5 + Polynomial.C (4201/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-79579/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (1937/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (-423243/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (37001/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (169833/31280 : ℚ)*Polynomial.X^11 + Polynomial.C (-140229/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (28107/1840 : ℚ)*Polynomial.X^13 + Polynomial.C (-1078489/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (981/368 : ℚ)*Polynomial.X^15
theorem eval3 (a : ℝ) (h : rf1789.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1789.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1789.rational a+Real.sqrt 2*evalQPoly rf1789.irrational a)/evalQPoly rf1789.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1789,rf1650]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/62560 : ℚ)*Polynomial.X^1 + Polynomial.C (151/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/595 : ℚ)*Polynomial.X^3 + Polynomial.C (333/6440 : ℚ)*Polynomial.X^4 + Polynomial.C (57203/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-10317/1288 : ℚ)*Polynomial.X^6 + Polynomial.C (1483549/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1515859/6440 : ℚ)*Polynomial.X^8 + Polynomial.C (156478093/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (-169486003/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (6402678/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-243626049/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (11618201/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (3753967/3128 : ℚ)*Polynomial.X^14 + Polynomial.C (-10953527/5474 : ℚ)*Polynomial.X^15 + Polynomial.C (28793787/21896 : ℚ)*Polynomial.X^16 + Polynomial.C (-30977641/87584 : ℚ)*Polynomial.X^17
theorem eval4 (a : ℝ) (h : rf1696.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1696.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1696.rational a+Real.sqrt 2*evalQPoly rf1696.irrational a)/evalQPoly rf1696.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1696,rf1650]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/875840 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/87584 : ℚ)*Polynomial.X^2 + Polynomial.C (143/218960 : ℚ)*Polynomial.X^3 + Polynomial.C (9/3680 : ℚ)*Polynomial.X^4 + Polynomial.C (-1375/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (41891/87584 : ℚ)*Polynomial.X^6 + Polynomial.C (-470791/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (199763/31280 : ℚ)*Polynomial.X^8 + Polynomial.C (-167684/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (4709973/437920 : ℚ)*Polynomial.X^10 + Polynomial.C (3638737/218960 : ℚ)*Polynomial.X^11 + Polynomial.C (-34490991/437920 : ℚ)*Polynomial.X^12 + Polynomial.C (15668521/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-65538691/437920 : ℚ)*Polynomial.X^14 + Polynomial.C (2730433/31280 : ℚ)*Polynomial.X^15 + Polynomial.C (-544593/25024 : ℚ)*Polynomial.X^16
theorem eval5 (a : ℝ) (h : rf1743.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1743.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1743.rational a+Real.sqrt 2*evalQPoly rf1743.irrational a)/evalQPoly rf1743.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1743,rf1650]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/31280 : ℚ)*Polynomial.X^1 + Polynomial.C (-107/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (2441/218960 : ℚ)*Polynomial.X^3 + Polynomial.C (-2183/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-16669/43792 : ℚ)*Polynomial.X^5 + Polynomial.C (655859/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-8941559/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (4853607/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-16765317/31280 : ℚ)*Polynomial.X^9 + Polynomial.C (127010507/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-394348349/218960 : ℚ)*Polynomial.X^11 + Polynomial.C (107513033/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-62665079/43792 : ℚ)*Polynomial.X^13 + Polynomial.C (805977/1288 : ℚ)*Polynomial.X^14 + Polynomial.C (-319617/2576 : ℚ)*Polynomial.X^15
theorem eval6 (a : ℝ) (h : rf1811.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1811.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1811.rational a+Real.sqrt 2*evalQPoly rf1811.irrational a)/evalQPoly rf1811.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1811,rf1650]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-109/218960 : ℚ)*Polynomial.X^2 + Polynomial.C (295/43792 : ℚ)*Polynomial.X^3 + Polynomial.C (-7397/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-29713/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (693487/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (-5238241/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (5001083/43792 : ℚ)*Polynomial.X^8 + Polynomial.C (-86234487/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (225970649/218960 : ℚ)*Polynomial.X^10 + Polynomial.C (-91405739/43792 : ℚ)*Polynomial.X^11 + Polynomial.C (30774039/9520 : ℚ)*Polynomial.X^12 + Polynomial.C (-814509499/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (656690789/218960 : ℚ)*Polynomial.X^14 + Polynomial.C (-331209803/218960 : ℚ)*Polynomial.X^15 + Polynomial.C (15828361/43792 : ℚ)*Polynomial.X^16
theorem eval7 (a : ℝ) (h : rf1765.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1765.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1765.rational a+Real.sqrt 2*evalQPoly rf1765.irrational a)/evalQPoly rf1765.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1765,rf1650]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/87584 : ℚ)*Polynomial.X^1 + Polynomial.C (3/12880 : ℚ)*Polynomial.X^2 + Polynomial.C (-583/437920 : ℚ)*Polynomial.X^3 + Polynomial.C (-17/6440 : ℚ)*Polynomial.X^4 + Polynomial.C (4269/62560 : ℚ)*Polynomial.X^5 + Polynomial.C (-85083/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (544993/437920 : ℚ)*Polynomial.X^7 + Polynomial.C (-3781/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (169237/87584 : ℚ)*Polynomial.X^9 + Polynomial.C (122603/31280 : ℚ)*Polynomial.X^10 + Polynomial.C (-6912317/437920 : ℚ)*Polynomial.X^11 + Polynomial.C (80069/3128 : ℚ)*Polynomial.X^12 + Polynomial.C (-9934623/437920 : ℚ)*Polynomial.X^13 + Polynomial.C (2815/272 : ℚ)*Polynomial.X^14 + Polynomial.C (-22911/12512 : ℚ)*Polynomial.X^15
theorem eval8 (a : ℝ) (h : rf1834.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1834.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1834.rational a+Real.sqrt 2*evalQPoly rf1834.irrational a)/evalQPoly rf1834.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1834,rf1650]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (149/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-831/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (397/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (11861/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-123111/15640 : ℚ)*Polynomial.X^6 + Polynomial.C (39217/782 : ℚ)*Polynomial.X^7 + Polynomial.C (-324519/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (3585933/6440 : ℚ)*Polynomial.X^9 + Polynomial.C (-118410333/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (80003689/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-71982717/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (78021343/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-229419/1288 : ℚ)*Polynomial.X^14
theorem eval9 (a : ℝ) (h : rf1880.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1880.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1880.rational a+Real.sqrt 2*evalQPoly rf1880.irrational a)/evalQPoly rf1880.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1880,rf1650]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (-89/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1569/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-251/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-92409/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (87489/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (-4210263/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (43045/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-3746327/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (1030529/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (60045723/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-1542917/1190 : ℚ)*Polynomial.X^12 + Polynomial.C (167842149/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-10741417/10948 : ℚ)*Polynomial.X^14 + Polynomial.C (858409/3128 : ℚ)*Polynomial.X^15
theorem eval10 (a : ℝ) (h : rf1856.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1856.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1856.rational a+Real.sqrt 2*evalQPoly rf1856.irrational a)/evalQPoly rf1856.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1856,rf1650]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/437920 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/31280 : ℚ)*Polynomial.X^1 + Polynomial.C (15/87584 : ℚ)*Polynomial.X^2 + Polynomial.C (3/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (-4831/437920 : ℚ)*Polynomial.X^4 + Polynomial.C (20063/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-185309/437920 : ℚ)*Polynomial.X^6 + Polynomial.C (13775/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (-1014229/437920 : ℚ)*Polynomial.X^8 + Polynomial.C (305799/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (326799/62560 : ℚ)*Polynomial.X^10 + Polynomial.C (-369759/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (10529203/437920 : ℚ)*Polynomial.X^12 + Polynomial.C (-3842431/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (64707/12512 : ℚ)*Polynomial.X^14
theorem eval11 (a : ℝ) (h : rf1903.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1903.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1903.rational a+Real.sqrt 2*evalQPoly rf1903.irrational a)/evalQPoly rf1903.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1903,rf1650]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even058
