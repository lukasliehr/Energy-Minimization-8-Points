import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even077
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1669.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (15/21896 : ℚ)*Polynomial.X^3 + Polynomial.C (47/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (-9063/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (24359/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-21987/15640 : ℚ)*Polynomial.X^7 + Polynomial.C (148387/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-223341/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-275151/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (276007/15640 : ℚ)*Polynomial.X^11 + Polynomial.C (-181123/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (1557683/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-125423/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (-286471/109480 : ℚ)*Polynomial.X^15 + Polynomial.C (7727/7820 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1669.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1669.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1669.rational a+Real.sqrt 2*evalQPoly rf1669.irrational a)/evalQPoly rf1669.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1669,rf1669]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (3/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (197/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-106/805 : ℚ)*Polynomial.X^5 + Polynomial.C (13537/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-20369/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-4125/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (265927/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-72825/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-9992/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (58955/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-117224/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-25307/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (201/85 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1693.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1693.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1693.rational a+Real.sqrt 2*evalQPoly rf1693.irrational a)/evalQPoly rf1693.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1693,rf1669]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (19/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-31/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (10011/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-41801/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (1899/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-1424/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-183307/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (313377/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-54/23 : ℚ)*Polynomial.X^11 + Polynomial.C (4965/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (33937/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-9/184 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1739.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1739.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1739.rational a+Real.sqrt 2*evalQPoly rf1739.irrational a)/evalQPoly rf1739.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1739,rf1669]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (0 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-24/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (1209/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-1864/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-2306/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (7848/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-79/230 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1808.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1808.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1808.rational a+Real.sqrt 2*evalQPoly rf1808.irrational a)/evalQPoly rf1808.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1808,rf1669]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-611/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (8937/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-6357/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (21989/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-79377/21896 : ℚ)*Polynomial.X^7 + Polynomial.C (496793/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (60897/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-193643/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (850783/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (-5239617/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (995837/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-466363/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (54811/15640 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1715.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1715.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1715.rational a+Real.sqrt 2*evalQPoly rf1715.irrational a)/evalQPoly rf1715.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1715,rf1669]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (3/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/595 : ℚ)*Polynomial.X^3 + Polynomial.C (1798/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-15143/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (15902/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-12113/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-6441/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (603049/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-144699/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-111847/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (273857/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-14543/782 : ℚ)*Polynomial.X^13 + Polynomial.C (23709/3910 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1762.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1762.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1762.rational a+Real.sqrt 2*evalQPoly rf1762.irrational a)/evalQPoly rf1762.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1762,rf1669]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (37/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (59/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-9837/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (43851/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-24733/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (23447/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (99063/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-496957/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (408277/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-19851/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (271861/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-381/920 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1830.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1830.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1830.rational a+Real.sqrt 2*evalQPoly rf1830.irrational a)/evalQPoly rf1830.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1830,rf1669]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (2/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (79/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-1525/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (15429/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-16659/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (2236/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (96027/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-121654/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (41789/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-72831/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (350733/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-3919/3910 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1784.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1784.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1784.rational a+Real.sqrt 2*evalQPoly rf1784.irrational a)/evalQPoly rf1784.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1784,rf1669]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (813/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-2819/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (647/1190 : ℚ)*Polynomial.X^6 + Polynomial.C (-2451/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-76079/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (15968/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-23652/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-7402/805 : ℚ)*Polynomial.X^11 + Polynomial.C (178427/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-21297/3910 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1853.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1853.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1853.rational a+Real.sqrt 2*evalQPoly rf1853.irrational a)/evalQPoly rf1853.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1853,rf1669]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-147/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (5791/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-3001/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (22453/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (44923/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-57737/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (60933/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-157603/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (37/92 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1899.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1899.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1899.rational a+Real.sqrt 2*evalQPoly rf1899.irrational a)/evalQPoly rf1899.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1899,rf1669]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (1/2380 : ℚ)*Polynomial.X^2 + Polynomial.C (279/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-401/6440 : ℚ)*Polynomial.X^4 + Polynomial.C (5677/15640 : ℚ)*Polynomial.X^5 + Polynomial.C (-37701/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (17091/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-237849/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-116407/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (67603/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (-181699/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (1452569/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-44797/15640 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1875.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1875.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1875.rational a+Real.sqrt 2*evalQPoly rf1875.irrational a)/evalQPoly rf1875.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1875,rf1669]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (771/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-563/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (17473/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-19137/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-34163/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (66646/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2004/391 : ℚ)*Polynomial.X^9 + Polynomial.C (-1373/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (2326/595 : ℚ)*Polynomial.X^11 + Polynomial.C (-7493/3910 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1922.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1922.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1922.rational a+Real.sqrt 2*evalQPoly rf1922.irrational a)/evalQPoly rf1922.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1922,rf1669]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even077
