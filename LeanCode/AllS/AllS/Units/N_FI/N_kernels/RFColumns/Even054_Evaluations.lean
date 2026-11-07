import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even054
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1325.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-71/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (63/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (-981/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-4729/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (15587/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-5507/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-524833/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (137478/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-24641/6440 : ℚ)*Polynomial.X^12 + Polynomial.C (-75891/7820 : ℚ)*Polynomial.X^13 + Polynomial.C (261841/21896 : ℚ)*Polynomial.X^14 + Polynomial.C (-12671/3910 : ℚ)*Polynomial.X^15 + Polynomial.C (-287223/109480 : ℚ)*Polynomial.X^16 + Polynomial.C (30143/54740 : ℚ)*Polynomial.X^17
theorem eval0 (a : ℝ) (h : rf1325.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1325.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1325.rational a+Real.sqrt 2*evalQPoly rf1325.irrational a)/evalQPoly rf1325.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1325,rf1325]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (47/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (361/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-3939/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (4502/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-1237/1564 : ℚ)*Polynomial.X^7 + Polynomial.C (3891/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (4559/3128 : ℚ)*Polynomial.X^9 + Polynomial.C (-76736/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (809427/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-9651/3220 : ℚ)*Polynomial.X^12 + Polynomial.C (-5277/1955 : ℚ)*Polynomial.X^13 + Polynomial.C (36086/13685 : ℚ)*Polynomial.X^14 + Polynomial.C (3779/27370 : ℚ)*Polynomial.X^15 + Polynomial.C (-43/85 : ℚ)*Polynomial.X^16
theorem eval1 (a : ℝ) (h : rf1344.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1344.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1344.rational a+Real.sqrt 2*evalQPoly rf1344.irrational a)/evalQPoly rf1344.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1344,rf1325]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-33/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (8213/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-5413/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (7247/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (9953/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-103923/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (871/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (4461/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (-4874/2737 : ℚ)*Polynomial.X^13 + Polynomial.C (24543/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (369/644 : ℚ)*Polynomial.X^15
theorem eval2 (a : ℝ) (h : rf1380.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1380.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1380.rational a+Real.sqrt 2*evalQPoly rf1380.irrational a)/evalQPoly rf1380.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1380,rf1325]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (0 : ℚ)*Polynomial.X^5 + Polynomial.C (0 : ℚ)*Polynomial.X^6 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-2/805 : ℚ)*Polynomial.X^8 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-402/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-106/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (1514/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-1882/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (6/115 : ℚ)*Polynomial.X^14
theorem eval3 (a : ℝ) (h : rf1434.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1434.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1434.rational a+Real.sqrt 2*evalQPoly rf1434.irrational a)/evalQPoly rf1434.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1434,rf1325]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (87/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-951/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (541/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (26939/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-3797/3128 : ℚ)*Polynomial.X^7 + Polynomial.C (42061/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (32263/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (-1401627/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (2073217/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-542109/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-2032557/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (2594681/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-1277529/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (124979/109480 : ℚ)*Polynomial.X^16
theorem eval4 (a : ℝ) (h : rf1361.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1361.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1361.rational a+Real.sqrt 2*evalQPoly rf1361.irrational a)/evalQPoly rf1361.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1361,rf1325]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (-333/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (3901/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-9767/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (56029/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-4243/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-10133/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (80749/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-1407599/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (139799/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-21657/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-19391/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (6761/1955 : ℚ)*Polynomial.X^14 + Polynomial.C (-3367/3910 : ℚ)*Polynomial.X^15
theorem eval5 (a : ℝ) (h : rf1398.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1398.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1398.rational a+Real.sqrt 2*evalQPoly rf1398.irrational a)/evalQPoly rf1398.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1398,rf1325]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (13/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (2/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-7277/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (5434/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-293/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-8796/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (14257/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-20064/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-23811/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (54982/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-225707/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (1082/805 : ℚ)*Polynomial.X^14
theorem eval6 (a : ℝ) (h : rf1451.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1451.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1451.rational a+Real.sqrt 2*evalQPoly rf1451.irrational a)/evalQPoly rf1451.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1451,rf1325]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (47/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (86/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-333/4760 : ℚ)*Polynomial.X^5 + Polynomial.C (411/1190 : ℚ)*Polynomial.X^6 + Polynomial.C (-105517/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (430/391 : ℚ)*Polynomial.X^8 + Polynomial.C (29909/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (-21215/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (710253/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (17580/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-1743913/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (329813/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (-264239/109480 : ℚ)*Polynomial.X^15
theorem eval7 (a : ℝ) (h : rf1415.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1415.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1415.rational a+Real.sqrt 2*evalQPoly rf1415.irrational a)/evalQPoly rf1415.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1415,rf1325]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (202/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3211/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (5123/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-674/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-3175/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (12461/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (-14271/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-972/391 : ℚ)*Polynomial.X^11 + Polynomial.C (119993/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-103212/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (4443/1955 : ℚ)*Polynomial.X^14
theorem eval8 (a : ℝ) (h : rf1469.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1469.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1469.rational a+Real.sqrt 2*evalQPoly rf1469.irrational a)/evalQPoly rf1469.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1469,rf1325]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-467/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (5303/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-452/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-923/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-166/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (16589/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-35367/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-38106/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (3309/782 : ℚ)*Polynomial.X^12 + Polynomial.C (-1355/644 : ℚ)*Polynomial.X^13
theorem eval9 (a : ℝ) (h : rf1505.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1505.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1505.rational a+Real.sqrt 2*evalQPoly rf1505.irrational a)/evalQPoly rf1505.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1505,rf1325]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-38/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2129/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-9621/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (4903/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (6122/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-19804/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (514313/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-56111/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-45772/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (6819/2737 : ℚ)*Polynomial.X^13 + Polynomial.C (3363/7820 : ℚ)*Polynomial.X^14
theorem eval10 (a : ℝ) (h : rf1486.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1486.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1486.rational a+Real.sqrt 2*evalQPoly rf1486.irrational a)/evalQPoly rf1486.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1486,rf1325]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (359/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-93/805 : ℚ)*Polynomial.X^4 + Polynomial.C (2571/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-14477/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (13978/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (70537/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-165819/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (276819/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-269147/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (21671/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (-5411/3910 : ℚ)*Polynomial.X^13
theorem eval11 (a : ℝ) (h : rf1523.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1523.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1523.rational a+Real.sqrt 2*evalQPoly rf1523.irrational a)/evalQPoly rf1523.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1523,rf1325]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even054
