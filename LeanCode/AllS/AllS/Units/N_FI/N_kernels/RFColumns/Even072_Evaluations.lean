import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even072
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1664.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-199/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (8443/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-1657/4760 : ℚ)*Polynomial.X^6 + Polynomial.C (48179/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-16256/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (39621/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (124371/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-85567/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (108543/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-175017/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (136269/15640 : ℚ)*Polynomial.X^14 + Polynomial.C (175381/54740 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1664.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1664.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1664.rational a+Real.sqrt 2*evalQPoly rf1664.irrational a)/evalQPoly rf1664.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1664,rf1664]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (24/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-13/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (-74/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1614/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-57/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-14976/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (4077/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (69519/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-117403/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (14517/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (699/85 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1688.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1688.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1688.rational a+Real.sqrt 2*evalQPoly rf1688.irrational a)/evalQPoly rf1688.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1688,rf1664]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (43/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (48/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-3201/15640 : ℚ)*Polynomial.X^5 + Polynomial.C (9217/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-4601/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-7391/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (49305/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-19991/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (75807/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-8593/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (1227/1288 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1734.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1734.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1734.rational a+Real.sqrt 2*evalQPoly rf1734.irrational a)/evalQPoly rf1734.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1734,rf1664]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (41/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (73/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^7 + Polynomial.C (1077/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-1291/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-10273/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (58516/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-528/115 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1803.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1803.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1803.rational a+Real.sqrt 2*evalQPoly rf1803.irrational a)/evalQPoly rf1803.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1803,rf1664]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (83/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (88/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-9839/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (51669/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-150733/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (29861/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-8707/15640 : ℚ)*Polynomial.X^8 + Polynomial.C (-7221/1288 : ℚ)*Polynomial.X^9 + Polynomial.C (1343793/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-139453/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (50917/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (-901673/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (1467273/109480 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1710.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1710.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1710.rational a+Real.sqrt 2*evalQPoly rf1710.irrational a)/evalQPoly rf1710.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1710,rf1664]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (3/170 : ℚ)*Polynomial.X^5 + Polynomial.C (-1026/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-3/805 : ℚ)*Polynomial.X^7 + Polynomial.C (621/595 : ℚ)*Polynomial.X^8 + Polynomial.C (-51378/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (120291/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (82464/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-45466/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (79751/3910 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1757.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1757.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1757.rational a+Real.sqrt 2*evalQPoly rf1757.irrational a)/evalQPoly rf1757.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1757,rf1664]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (13/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-647/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (25713/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-12417/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (20558/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (3863/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-551681/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (27539/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-16411/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (671/1190 : ℚ)*Polynomial.X^11 + Polynomial.C (-9053/6440 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1825.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1825.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1825.rational a+Real.sqrt 2*evalQPoly rf1825.irrational a)/evalQPoly rf1825.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1825,rf1664]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (1/1190 : ℚ)*Polynomial.X^2 + Polynomial.C (6/391 : ℚ)*Polynomial.X^3 + Polynomial.C (-8191/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (32001/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-14853/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (6864/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (6443/3220 : ℚ)*Polynomial.X^8 + Polynomial.C (-363479/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (4575/322 : ℚ)*Polynomial.X^10 + Polynomial.C (-13894/805 : ℚ)*Polynomial.X^11 + Polynomial.C (3429/460 : ℚ)*Polynomial.X^12 + Polynomial.C (-37129/54740 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1779.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1779.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1779.rational a+Real.sqrt 2*evalQPoly rf1779.irrational a)/evalQPoly rf1779.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1779,rf1664]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-11/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (163/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-141/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (3267/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-33/85 : ℚ)*Polynomial.X^8 + Polynomial.C (-915/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (1983/805 : ℚ)*Polynomial.X^10 + Polynomial.C (-845/391 : ℚ)*Polynomial.X^11 + Polynomial.C (-2744/1955 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1848.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1848.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1848.rational a+Real.sqrt 2*evalQPoly rf1848.irrational a)/evalQPoly rf1848.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1848,rf1664]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (31/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^2 + Polynomial.C (-1753/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (3484/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-22007/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (11486/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (47349/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-172383/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (379647/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-9307/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-61/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1894.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1894.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1894.rational a+Real.sqrt 2*evalQPoly rf1894.irrational a)/evalQPoly rf1894.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1894,rf1664]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (1/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (127/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-7467/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (1964/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (246/805 : ℚ)*Polynomial.X^6 + Polynomial.C (-25794/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (47967/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (35822/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-1691/238 : ℚ)*Polynomial.X^10 + Polynomial.C (75819/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-67143/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1870.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1870.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1870.rational a+Real.sqrt 2*evalQPoly rf1870.irrational a)/evalQPoly rf1870.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1870,rf1664]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (29/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (39/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-191/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (760/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-1522/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-22543/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (38987/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (58403/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-23967/3910 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1917.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1917.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1917.rational a+Real.sqrt 2*evalQPoly rf1917.irrational a)/evalQPoly rf1917.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1917,rf1664]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even072
