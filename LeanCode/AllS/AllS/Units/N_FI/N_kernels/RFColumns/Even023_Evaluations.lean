import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even023
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1054.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (673/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-209/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3352/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (3466/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-25681/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (42222/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-232111/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (137859/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (555997/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-92549/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-6167/782 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf1054.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1054.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1054.rational a+Real.sqrt 2*evalQPoly rf1054.irrational a)/evalQPoly rf1054.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1054,rf1054]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (293/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-509/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-4959/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (18471/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-55803/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (66071/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (41183/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-157441/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (964641/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-151889/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-515/68 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf1069.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1069.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1069.rational a+Real.sqrt 2*evalQPoly rf1069.irrational a)/evalQPoly rf1069.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1069,rf1054]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (21/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (81/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-3709/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1644/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-15531/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (84992/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-93915/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (22349/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-1443/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (13/46 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf1097.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1097.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1097.rational a+Real.sqrt 2*evalQPoly rf1097.irrational a)/evalQPoly rf1097.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1097,rf1054]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-29/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (131/805 : ℚ)*Polynomial.X^5 + Polynomial.C (-2521/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (1212/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (8383/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (-90053/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (317/92 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1139.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1139.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1139.rational a+Real.sqrt 2*evalQPoly rf1139.irrational a)/evalQPoly rf1139.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1139,rf1054]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (260/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-9552/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (78573/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-16021/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (926503/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-308633/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (578957/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (463843/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-17753/782 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf1082.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1082.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1082.rational a+Real.sqrt 2*evalQPoly rf1082.irrational a)/evalQPoly rf1082.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1082,rf1054]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^1 + Polynomial.C (327/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-198/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3107/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (13683/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-94489/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (74804/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (66197/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-84763/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (295373/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-9534/391 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf1111.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1111.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1111.rational a+Real.sqrt 2*evalQPoly rf1111.irrational a)/evalQPoly rf1111.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1111,rf1054]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (262/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-5167/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (12209/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-11801/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (103518/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-631523/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (12783/1610 : ℚ)*Polynomial.X^9 + Polynomial.C (-85/92 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf1152.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1152.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1152.rational a+Real.sqrt 2*evalQPoly rf1152.irrational a)/evalQPoly rf1152.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1152,rf1054]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (57/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-93/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (716/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1709/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-30082/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (11579/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (-208868/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (12693/644 : ℚ)*Polynomial.X^9 + Polynomial.C (-195359/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (10541/1564 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf1124.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1124.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1124.rational a+Real.sqrt 2*evalQPoly rf1124.irrational a)/evalQPoly rf1124.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1124,rf1054]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (2/1955 : ℚ)*Polynomial.X^1 + Polynomial.C (-291/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (4937/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-9776/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (30517/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (7256/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-15999/3220 : ℚ)*Polynomial.X^8 + Polynomial.C (2558/391 : ℚ)*Polynomial.X^9 + Polynomial.C (-2541/1564 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf1166.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1166.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1166.rational a+Real.sqrt 2*evalQPoly rf1166.irrational a)/evalQPoly rf1166.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1166,rf1054]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (1/1190 : ℚ)*Polynomial.X^1 + Polynomial.C (-96/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (208/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (423/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-17669/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (11468/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-95988/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (35239/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-135/46 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf1194.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1194.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1194.rational a+Real.sqrt 2*evalQPoly rf1194.irrational a)/evalQPoly rf1194.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1194,rf1054]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (193/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-122/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-241/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (6703/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-34499/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (13798/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (113293/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-222507/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (15063/1564 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf1179.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1179.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1179.rational a+Real.sqrt 2*evalQPoly rf1179.irrational a)/evalQPoly rf1179.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1179,rf1054]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-78/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-142/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (127/595 : ℚ)*Polynomial.X^4 + Polynomial.C (-10656/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (13626/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2654/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-145833/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (2361/391 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf1208.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1208.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1208.rational a+Real.sqrt 2*evalQPoly rf1208.irrational a)/evalQPoly rf1208.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1208,rf1054]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even023
