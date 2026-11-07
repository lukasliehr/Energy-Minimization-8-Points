import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even039
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1310.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (19/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-613/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (17/644 : ℚ)*Polynomial.X^4 + Polynomial.C (-727/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (20359/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-19563/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (458373/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-1721229/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1487499/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (780847/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-25817/460 : ℚ)*Polynomial.X^12 + Polynomial.C (914559/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (31030/2737 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1310.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1310.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1310.rational a+Real.sqrt 2*evalQPoly rf1310.irrational a)/evalQPoly rf1310.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1310,rf1310]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (19/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (467/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-914/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (11703/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-25562/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (54289/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1573/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (-387147/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (60424/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-121369/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (-32323/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (789/34 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1329.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1329.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1329.rational a+Real.sqrt 2*evalQPoly rf1329.irrational a)/evalQPoly rf1329.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1329,rf1310]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (337/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-193/1564 : ℚ)*Polynomial.X^4 + Polynomial.C (27619/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-118493/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (53877/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-53255/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-204213/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1106467/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-1032691/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (2133/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1365.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1365.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1365.rational a+Real.sqrt 2*evalQPoly rf1365.irrational a)/evalQPoly rf1365.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1365,rf1310]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (13/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (97/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-206/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (1529/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-24882/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (38867/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (29611/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-23151/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (552763/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-320/23 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1419.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1419.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1419.rational a+Real.sqrt 2*evalQPoly rf1419.irrational a)/evalQPoly rf1419.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1419,rf1310]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (121/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-123/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (4309/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-9871/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-10053/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (794697/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-2116731/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (3244853/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-414979/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-706227/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (254673/5474 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1346.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1346.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1346.rational a+Real.sqrt 2*evalQPoly rf1346.irrational a)/evalQPoly rf1346.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1346,rf1310]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/782 : ℚ)*Polynomial.X^2 + Polynomial.C (753/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-689/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (14751/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-62413/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (30273/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-8383/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-512949/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (2054259/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-406749/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (47607/782 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1383.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1383.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1383.rational a+Real.sqrt 2*evalQPoly rf1383.irrational a)/evalQPoly rf1383.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1383,rf1310]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/1564 : ℚ)*Polynomial.X^2 + Polynomial.C (-367/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (551/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (12783/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-20275/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (267773/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-20423/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (436967/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (8949/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (-4131/644 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1436.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1436.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1436.rational a+Real.sqrt 2*evalQPoly rf1436.irrational a)/evalQPoly rf1436.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1436,rf1310]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (273/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-815/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-3279/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (6347/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (12289/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (-403147/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (1715873/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-1917589/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (860011/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-35043/10948 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1400.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1400.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1400.rational a+Real.sqrt 2*evalQPoly rf1400.irrational a)/evalQPoly rf1400.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1400,rf1310]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (8/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (-103/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (2003/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1644/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (31506/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-3943/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-116159/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (205713/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-35154/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (4319/782 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1454.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1454.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1454.rational a+Real.sqrt 2*evalQPoly rf1454.irrational a)/evalQPoly rf1454.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1454,rf1310]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (67/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-776/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (588/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-12108/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (4254/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-75976/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (132308/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-116066/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (503/161 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1490.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1490.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1490.rational a+Real.sqrt 2*evalQPoly rf1490.irrational a)/evalQPoly rf1490.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1490,rf1310]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/2380 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (933/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (43/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (-303/782 : ℚ)*Polynomial.X^5 + Polynomial.C (20021/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (29541/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-255813/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (193267/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (334353/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-20821/1564 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1471.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1471.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1471.rational a+Real.sqrt 2*evalQPoly rf1471.irrational a)/evalQPoly rf1471.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1471,rf1310]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (59/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-376/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (2628/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-13602/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (4742/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-15104/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-12564/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (210463/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-5567/391 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1508.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1508.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1508.rational a+Real.sqrt 2*evalQPoly rf1508.irrational a)/evalQPoly rf1508.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1508,rf1310]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even039
