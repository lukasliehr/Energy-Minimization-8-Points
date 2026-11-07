import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even022
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1053.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (5/43792 : ℚ)*Polynomial.X^2 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-543/31280 : ℚ)*Polynomial.X^4 + Polynomial.C (477/6440 : ℚ)*Polynomial.X^5 + Polynomial.C (20025/43792 : ℚ)*Polynomial.X^6 + Polynomial.C (-74189/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (8326139/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (-14257751/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (9521901/31280 : ℚ)*Polynomial.X^10 + Polynomial.C (-14004357/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (141035317/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-69191637/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (107110671/218960 : ℚ)*Polynomial.X^14 + Polynomial.C (-15025113/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (2580879/31280 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1053.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1053.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1053.rational a+Real.sqrt 2*evalQPoly rf1053.irrational a)/evalQPoly rf1053.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1053,rf1053]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/437920 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/31280 : ℚ)*Polynomial.X^2 + Polynomial.C (593/437920 : ℚ)*Polynomial.X^3 + Polynomial.C (-1551/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (31343/437920 : ℚ)*Polynomial.X^5 + Polynomial.C (-39961/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (59809/437920 : ℚ)*Polynomial.X^7 + Polynomial.C (3237/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-15821/19040 : ℚ)*Polynomial.X^9 + Polynomial.C (-22463/31280 : ℚ)*Polynomial.X^10 + Polynomial.C (1151867/437920 : ℚ)*Polynomial.X^11 + Polynomial.C (35391/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (-5557571/437920 : ℚ)*Polynomial.X^13 + Polynomial.C (429311/31280 : ℚ)*Polynomial.X^14 + Polynomial.C (-13069/2720 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1068.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1068.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1068.rational a+Real.sqrt 2*evalQPoly rf1068.irrational a)/evalQPoly rf1068.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1068,rf1053]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (41/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-7841/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-34929/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (154187/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-463056/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (13370599/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-32020839/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (25778003/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-6747493/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (33503257/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-15961/184 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1096.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1096.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1096.rational a+Real.sqrt 2*evalQPoly rf1096.irrational a)/evalQPoly rf1096.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1096,rf1053]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (249/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-21/782 : ℚ)*Polynomial.X^5 + Polynomial.C (521/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-2748/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (6217/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (265/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-66971/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (37206/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-175/68 : ℚ)*Polynomial.X^12 + Polynomial.C (203/230 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1138.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1138.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1138.rational a+Real.sqrt 2*evalQPoly rf1138.irrational a)/evalQPoly rf1138.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1138,rf1053]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (13/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/680 : ℚ)*Polynomial.X^2 + Polynomial.C (2727/218960 : ℚ)*Polynomial.X^3 + Polynomial.C (-101/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-169307/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (34817/4760 : ℚ)*Polynomial.X^6 + Polynomial.C (-8104457/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (47068/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-57257761/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (40213389/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-60867763/218960 : ℚ)*Polynomial.X^11 + Polynomial.C (-518571/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (59598191/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (-5663815/21896 : ℚ)*Polynomial.X^14 + Polynomial.C (2855171/31280 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1081.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1081.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1081.rational a+Real.sqrt 2*evalQPoly rf1081.irrational a)/evalQPoly rf1081.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1081,rf1053]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/437920 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/43792 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/437920 : ℚ)*Polynomial.X^2 + Polynomial.C (281/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-8399/437920 : ℚ)*Polynomial.X^4 + Polynomial.C (16937/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-13857/87584 : ℚ)*Polynomial.X^6 + Polynomial.C (-677/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (578379/437920 : ℚ)*Polynomial.X^8 + Polynomial.C (-712883/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (910121/437920 : ℚ)*Polynomial.X^10 + Polynomial.C (116597/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (-5462717/437920 : ℚ)*Polynomial.X^12 + Polynomial.C (318489/31280 : ℚ)*Polynomial.X^13 + Polynomial.C (-188713/62560 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1110.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1110.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1110.rational a+Real.sqrt 2*evalQPoly rf1110.irrational a)/evalQPoly rf1110.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1110,rf1053]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (57/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-279/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (1/68 : ℚ)*Polynomial.X^4 + Polynomial.C (863/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (-11/2 : ℚ)*Polynomial.X^6 + Polynomial.C (2391/85 : ℚ)*Polynomial.X^7 + Polynomial.C (-2474391/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (5315281/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-15372843/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (1443805/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (-467847/3220 : ℚ)*Polynomial.X^12 + Polynomial.C (8143/230 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1151.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1151.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1151.rational a+Real.sqrt 2*evalQPoly rf1151.irrational a)/evalQPoly rf1151.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1151,rf1053]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (11/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-64/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (31/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (16703/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-48429/15640 : ℚ)*Polynomial.X^6 + Polynomial.C (233074/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1726807/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (546797/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (-37357983/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (6917166/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-28565133/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (3670913/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-1599163/15640 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1123.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1123.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1123.rational a+Real.sqrt 2*evalQPoly rf1123.irrational a)/evalQPoly rf1123.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1123,rf1053]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-22/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (55/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-6481/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (131/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (6501/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-8311/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (33661/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (75883/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-50857/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (533/782 : ℚ)*Polynomial.X^12 + Polynomial.C (707/31280 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1165.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1165.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1165.rational a+Real.sqrt 2*evalQPoly rf1165.irrational a)/evalQPoly rf1165.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1165,rf1053]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-15/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (1/92 : ℚ)*Polynomial.X^3 + Polynomial.C (653/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-22759/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (191739/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-884147/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (2585791/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-9863653/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (520867/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-8525373/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (4647/92 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1193.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1193.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1193.rational a+Real.sqrt 2*evalQPoly rf1193.irrational a)/evalQPoly rf1193.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1193,rf1053]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (93/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-131/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2801/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (109883/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-168999/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (11877/595 : ℚ)*Polynomial.X^7 + Polynomial.C (-865289/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-360307/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (6355073/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-3091876/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (11032947/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1175081/15640 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1178.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1178.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1178.rational a+Real.sqrt 2*evalQPoly rf1178.irrational a)/evalQPoly rf1178.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1178,rf1053]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-239/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (4687/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-563/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-933/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (1985/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-22757/31280 : ℚ)*Polynomial.X^8 + Polynomial.C (2433/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (23659/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-17749/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (27363/31280 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1207.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1207.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1207.rational a+Real.sqrt 2*evalQPoly rf1207.irrational a)/evalQPoly rf1207.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1207,rf1053]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even022
