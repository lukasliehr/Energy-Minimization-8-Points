import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even052
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1323.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-381/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (8509/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-7605/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (45753/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-29717/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (4359/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (35409/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (-150033/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (298199/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-229933/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (2529/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (5427/7820 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1323.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1323.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1323.rational a+Real.sqrt 2*evalQPoly rf1323.irrational a)/evalQPoly rf1323.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1323,rf1323]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-198/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (2773/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-3883/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (5023/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (3393/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (-116303/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (65371/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (2283/1610 : ℚ)*Polynomial.X^11 + Polynomial.C (-8759/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-547/1190 : ℚ)*Polynomial.X^13 + Polynomial.C (61/85 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1342.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1342.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1342.rational a+Real.sqrt 2*evalQPoly rf1342.irrational a)/evalQPoly rf1342.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1342,rf1323]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-831/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (337/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-5907/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (2089/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-22579/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (66531/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-11911/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-8599/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (7/92 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1378.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1378.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1378.rational a+Real.sqrt 2*evalQPoly rf1378.irrational a)/evalQPoly rf1378.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1378,rf1323]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-24/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (1209/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-1864/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-2306/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (7848/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-79/230 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1432.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1432.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1432.rational a+Real.sqrt 2*evalQPoly rf1432.irrational a)/evalQPoly rf1432.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1432,rf1323]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (43/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (11/1610 : ℚ)*Polynomial.X^3 + Polynomial.C (-7559/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (4118/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-85469/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (160/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-137741/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-16693/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (764417/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-68175/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (1314739/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-87383/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (33191/15640 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1359.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1359.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1359.rational a+Real.sqrt 2*evalQPoly rf1359.irrational a)/evalQPoly rf1359.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1359,rf1323]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (11/805 : ℚ)*Polynomial.X^3 + Polynomial.C (-563/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (9431/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-14537/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-2493/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (16333/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-237259/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (6277/1610 : ℚ)*Polynomial.X^10 + Polynomial.C (2083/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (-103711/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (8299/3910 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1396.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1396.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1396.rational a+Real.sqrt 2*evalQPoly rf1396.irrational a)/evalQPoly rf1396.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1396,rf1323]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (38/595 : ℚ)*Polynomial.X^5 + Polynomial.C (-778/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (142/595 : ℚ)*Polynomial.X^7 + Polynomial.C (17237/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-9290/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (8105/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-314/391 : ℚ)*Polynomial.X^11 + Polynomial.C (-9/230 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1449.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1449.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1449.rational a+Real.sqrt 2*evalQPoly rf1449.irrational a)/evalQPoly rf1449.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1449,rf1323]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-463/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (6661/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-16839/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-491/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (24729/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-36147/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-60407/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (341469/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-489331/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (32587/6440 : ℚ)*Polynomial.X^12 + Polynomial.C (-24071/15640 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1413.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1413.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1413.rational a+Real.sqrt 2*evalQPoly rf1413.irrational a)/evalQPoly rf1413.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1413,rf1323]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (6/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-747/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (4997/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-14249/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (13689/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (711/782 : ℚ)*Polynomial.X^8 + Polynomial.C (-43052/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (99697/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-3692/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (679/1955 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1467.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1467.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1467.rational a+Real.sqrt 2*evalQPoly rf1467.irrational a)/evalQPoly rf1467.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1467,rf1323]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (39/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (929/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-4059/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1897/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-3117/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-12867/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (15763/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-133341/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (82251/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-9/92 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1503.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1503.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1503.rational a+Real.sqrt 2*evalQPoly rf1503.irrational a)/evalQPoly rf1503.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1503,rf1323]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-411/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (6073/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-272/805 : ℚ)*Polynomial.X^5 + Polynomial.C (1171/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (58/391 : ℚ)*Polynomial.X^7 + Polynomial.C (-86883/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (93073/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-46756/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (36167/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-5091/7820 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1484.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1484.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1484.rational a+Real.sqrt 2*evalQPoly rf1484.irrational a)/evalQPoly rf1484.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1484,rf1323]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (1/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-751/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (4133/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-1193/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-3483/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (44649/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-32036/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-5792/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (48759/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-4149/1955 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1521.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1521.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1521.rational a+Real.sqrt 2*evalQPoly rf1521.irrational a)/evalQPoly rf1521.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1521,rf1323]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even052
