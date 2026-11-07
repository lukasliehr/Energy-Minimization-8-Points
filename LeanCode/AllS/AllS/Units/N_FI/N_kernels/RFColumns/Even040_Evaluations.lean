import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even040
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1311.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-39/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (177/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-957/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (109/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (42029/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (64321/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-7096/391 : ℚ)*Polynomial.X^7 + Polynomial.C (1950833/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-15430013/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (100613/805 : ℚ)*Polynomial.X^10 + Polynomial.C (1376877/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-11971263/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (13790199/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (2530169/54740 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1311.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1311.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1311.rational a+Real.sqrt 2*evalQPoly rf1311.irrational a)/evalQPoly rf1311.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1311,rf1311]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (36/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-209/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (87/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (125/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (8123/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-3876/805 : ℚ)*Polynomial.X^6 + Polynomial.C (10179/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-76343/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-24588/595 : ℚ)*Polynomial.X^9 + Polynomial.C (1266681/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-305667/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (-1694599/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (7801/85 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1330.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1330.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1330.rational a+Real.sqrt 2*evalQPoly rf1330.irrational a)/evalQPoly rf1330.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1330,rf1311]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (7/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (39/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-2979/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (9330/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-84703/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (509178/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-7077/170 : ℚ)*Polynomial.X^8 + Polynomial.C (-3119/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (3276949/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-22767/391 : ℚ)*Polynomial.X^11 + Polynomial.C (4659/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1366.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1366.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1366.rational a+Real.sqrt 2*evalQPoly rf1366.irrational a)/evalQPoly rf1366.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1366,rf1311]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (3/391 : ℚ)*Polynomial.X^2 + Polynomial.C (638/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-7088/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (34694/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-106826/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (22432/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (17470/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-710127/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1145689/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-6362/115 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1420.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1420.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1420.rational a+Real.sqrt 2*evalQPoly rf1420.irrational a)/evalQPoly rf1420.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1420,rf1311]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/15640 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (106/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (9/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-6445/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (176247/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-36881/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-126878/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (6969173/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-18694663/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (3396919/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-3870259/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-2543103/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (20268757/109480 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1347.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1347.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1347.rational a+Real.sqrt 2*evalQPoly rf1347.irrational a)/evalQPoly rf1347.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1347,rf1311]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-347/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (197/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (-11663/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (43422/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-214927/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (4834/115 : ℚ)*Polynomial.X^7 + Polynomial.C (-614639/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-119949/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (7562777/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-761937/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (894859/3910 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1384.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1384.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1384.rational a+Real.sqrt 2*evalQPoly rf1384.irrational a)/evalQPoly rf1384.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1384,rf1311]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (12/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (1/161 : ℚ)*Polynomial.X^2 + Polynomial.C (-346/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (50/119 : ℚ)*Polynomial.X^4 + Polynomial.C (22128/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-196086/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (548804/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-771269/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (98020/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (8417/805 : ℚ)*Polynomial.X^10 + Polynomial.C (-20434/805 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1437.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1437.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1437.rational a+Real.sqrt 2*evalQPoly rf1437.irrational a)/evalQPoly rf1437.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1437,rf1311]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (37/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-449/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (367/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (-20523/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-20143/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (14052/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (16417/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (-6815813/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (7040009/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-3898439/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (3751651/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-1951377/109480 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1401.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1401.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1401.rational a+Real.sqrt 2*evalQPoly rf1401.irrational a)/evalQPoly rf1401.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1401,rf1311]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-33/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (297/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (4702/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-39072/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (123087/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-17869/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-197108/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (770269/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-267177/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (83433/3910 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1455.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1455.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1455.rational a+Real.sqrt 2*evalQPoly rf1455.irrational a)/evalQPoly rf1455.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1455,rf1311]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (99/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-524/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (31531/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-50684/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (250981/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-303668/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (306253/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-103556/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (10445/644 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1491.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1491.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1491.rational a+Real.sqrt 2*evalQPoly rf1491.irrational a)/evalQPoly rf1491.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1491,rf1311]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (71/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-773/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (3049/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (3889/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-44621/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (80331/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (27445/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-1106991/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (752291/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (43573/1564 : ℚ)*Polynomial.X^10 + Polynomial.C (-428701/7820 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1472.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1472.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1472.rational a+Real.sqrt 2*evalQPoly rf1472.irrational a)/evalQPoly rf1472.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1472,rf1311]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-18/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (179/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-892/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (7408/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-46976/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (127758/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-73796/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-312952/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (111646/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (-103999/1955 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1509.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1509.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1509.rational a+Real.sqrt 2*evalQPoly rf1509.irrational a)/evalQPoly rf1509.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1509,rf1311]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even040
