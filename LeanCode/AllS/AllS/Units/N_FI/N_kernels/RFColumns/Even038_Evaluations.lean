import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even038
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1309.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (11/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-223/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-283/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (1279/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-189951/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (245829/15640 : ℚ)*Polynomial.X^7 + Polynomial.C (-1321209/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (5746287/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-2242637/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (4030419/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (-1682683/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (2987659/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-3942531/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (450011/15640 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1309.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1309.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1309.rational a+Real.sqrt 2*evalQPoly rf1309.irrational a)/evalQPoly rf1309.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1309,rf1309]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/43792 : ℚ)*Polynomial.X^1 + Polynomial.C (381/218960 : ℚ)*Polynomial.X^2 + Polynomial.C (-107/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (143/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-1191/43792 : ℚ)*Polynomial.X^5 + Polynomial.C (33819/218960 : ℚ)*Polynomial.X^6 + Polynomial.C (-26109/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (16309/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (113489/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (-1358101/218960 : ℚ)*Polynomial.X^10 + Polynomial.C (74843/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (232133/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-3528933/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (10909/1360 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1328.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1328.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1328.rational a+Real.sqrt 2*evalQPoly rf1328.irrational a)/evalQPoly rf1328.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1328,rf1309]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (47/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (496/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-8131/15640 : ℚ)*Polynomial.X^5 + Polynomial.C (47352/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-39888/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (586426/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-1424033/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (1891399/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-782491/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (250758/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-5149/184 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1364.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1364.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1364.rational a+Real.sqrt 2*evalQPoly rf1364.irrational a)/evalQPoly rf1364.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1364,rf1309]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-57/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (3481/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-999/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (16431/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-29369/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (31281/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (1503/476 : ℚ)*Polynomial.X^9 + Polynomial.C (-420751/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (65261/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-3199/920 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1418.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1418.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1418.rational a+Real.sqrt 2*evalQPoly rf1418.irrational a)/evalQPoly rf1418.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1418,rf1309]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/6440 : ℚ)*Polynomial.X^1 + Polynomial.C (43/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (11/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2993/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (275469/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-687657/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (553736/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-4794997/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (13649663/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-5480743/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (15297/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (5524937/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-2483685/21896 : ℚ)*Polynomial.X^13 + Polynomial.C (360287/7820 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1345.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1345.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1345.rational a+Real.sqrt 2*evalQPoly rf1345.irrational a)/evalQPoly rf1345.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1345,rf1309]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/43792 : ℚ)*Polynomial.X^1 + Polynomial.C (25/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-737/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (1129/31280 : ℚ)*Polynomial.X^4 + Polynomial.C (-45519/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (51721/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-149929/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (922631/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (6247/31280 : ℚ)*Polynomial.X^9 + Polynomial.C (-247577/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (3775539/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-216493/6256 : ℚ)*Polynomial.X^12 + Polynomial.C (422513/31280 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1382.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1382.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1382.rational a+Real.sqrt 2*evalQPoly rf1382.irrational a)/evalQPoly rf1382.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1382,rf1309]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (-201/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (579/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (17133/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-1461/782 : ℚ)*Polynomial.X^5 + Polynomial.C (687/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-171133/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (7219273/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-5134627/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (947179/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-148417/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (9741/920 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1435.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1435.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1435.rational a+Real.sqrt 2*evalQPoly rf1435.irrational a)/evalQPoly rf1435.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1435,rf1309]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (-43/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-537/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (17201/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-2747/2380 : ℚ)*Polynomial.X^5 + Polynomial.C (9241/1610 : ℚ)*Polynomial.X^6 + Polynomial.C (-572743/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (6237081/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-317157/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (9392553/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-1363999/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (2427883/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (-271647/7820 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1399.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1399.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1399.rational a+Real.sqrt 2*evalQPoly rf1399.irrational a)/evalQPoly rf1399.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1399,rf1309]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (-167/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (111/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (-939/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (9143/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-28017/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (41287/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (20067/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-355379/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (690841/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-14701/3128 : ℚ)*Polynomial.X^11 + Polynomial.C (8379/7820 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1453.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1453.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1453.rational a+Real.sqrt 2*evalQPoly rf1453.irrational a)/evalQPoly rf1453.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1453,rf1309]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2380 : ℚ)*Polynomial.X^1 + Polynomial.C (27/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (923/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-81/238 : ℚ)*Polynomial.X^4 + Polynomial.C (9663/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-59589/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (865679/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-3310187/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (803889/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-2872997/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (1613/92 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1489.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1489.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1489.rational a+Real.sqrt 2*evalQPoly rf1489.irrational a)/evalQPoly rf1489.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1489,rf1309]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (-67/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-49/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (40057/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-28316/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (3831/595 : ℚ)*Polynomial.X^6 + Polynomial.C (-27873/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-53449/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (1000457/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-2047303/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (140628/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (-461643/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1470.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1470.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1470.rational a+Real.sqrt 2*evalQPoly rf1470.irrational a)/evalQPoly rf1470.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1470,rf1309]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (19/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-121/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (431/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-1543/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (10653/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-34763/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (43693/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (69119/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-87385/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (686879/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-50783/15640 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1507.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1507.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1507.rational a+Real.sqrt 2*evalQPoly rf1507.irrational a)/evalQPoly rf1507.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1507,rf1309]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even038
