import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even030
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1061.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-209/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (923/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-1459/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-5863/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (3279/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (-39243/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-3549/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (16793/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-3359/1564 : ℚ)*Polynomial.X^12 + Polynomial.C (-29669/27370 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf1061.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1061.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1061.rational a+Real.sqrt 2*evalQPoly rf1061.irrational a)/evalQPoly rf1061.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1061,rf1061]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (22/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (1/805 : ℚ)*Polynomial.X^5 + Polynomial.C (-2528/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (549/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-7368/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-26737/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (58083/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-2746/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-202/85 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf1076.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1076.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1076.rational a+Real.sqrt 2*evalQPoly rf1076.irrational a)/evalQPoly rf1076.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1076,rf1061]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-33/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (1489/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-1543/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1141/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (-11343/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (47391/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (584/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-359/644 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf1104.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1104.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1104.rational a+Real.sqrt 2*evalQPoly rf1104.irrational a)/evalQPoly rf1104.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1104,rf1061]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (1/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-61/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-52/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2197/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-3469/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-6751/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (223/230 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1146.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1146.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1146.rational a+Real.sqrt 2*evalQPoly rf1146.irrational a)/evalQPoly rf1146.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1146,rf1061]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (2/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/2380 : ℚ)*Polynomial.X^4 + Polynomial.C (-8/391 : ℚ)*Polynomial.X^5 + Polynomial.C (3501/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-5816/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (35983/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-37712/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (85977/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (46934/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-238857/54740 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf1089.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1089.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1089.rational a+Real.sqrt 2*evalQPoly rf1089.irrational a)/evalQPoly rf1089.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1089,rf1061]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (25/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-144/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-412/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (14968/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-22993/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2988/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (1737/230 : ℚ)*Polynomial.X^10 + Polynomial.C (-13139/1955 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf1118.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1118.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1118.rational a+Real.sqrt 2*evalQPoly rf1118.irrational a)/evalQPoly rf1118.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1118,rf1061]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (216/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1931/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (202/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (4343/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-1856/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-51899/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (25209/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-3253/3220 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf1159.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1159.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1159.rational a+Real.sqrt 2*evalQPoly rf1159.irrational a)/evalQPoly rf1159.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1159,rf1061]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/1190 : ℚ)*Polynomial.X^3 + Polynomial.C (2963/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-4383/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (319/782 : ℚ)*Polynomial.X^6 + Polynomial.C (6173/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1077/340 : ℚ)*Polynomial.X^8 + Polynomial.C (154871/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-192007/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (4411/27370 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf1131.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1131.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1131.rational a+Real.sqrt 2*evalQPoly rf1131.irrational a)/evalQPoly rf1131.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1131,rf1061]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (19/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (348/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-2818/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (7678/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-523/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-25248/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (80139/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-1758/1955 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf1173.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1173.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1173.rational a+Real.sqrt 2*evalQPoly rf1173.irrational a)/evalQPoly rf1173.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1173,rf1061]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (468/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2439/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (683/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (7284/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-26304/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (44469/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-37/322 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf1201.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1201.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1201.rational a+Real.sqrt 2*evalQPoly rf1201.irrational a)/evalQPoly rf1201.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1201,rf1061]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (33/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-48/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (273/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (26/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-14747/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (288/391 : ℚ)*Polynomial.X^7 + Polynomial.C (37411/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-3683/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (9107/7820 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf1186.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1186.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1186.rational a+Real.sqrt 2*evalQPoly rf1186.irrational a)/evalQPoly rf1186.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1186,rf1061]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (22/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-99/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-424/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (757/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-5378/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-10821/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (3308/1955 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf1215.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1215.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1215.rational a+Real.sqrt 2*evalQPoly rf1215.irrational a)/evalQPoly rf1215.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1215,rf1061]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even030
