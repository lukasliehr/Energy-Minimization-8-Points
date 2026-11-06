import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even026
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1057.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (5/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-99/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-97/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (11111/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-19288/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (13091/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-35327/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (103209/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-342199/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (30171/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-4923/460 : ℚ)*Polynomial.X^12 + Polynomial.C (179933/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (17427/5474 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1057.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1057.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1057.rational a+Real.sqrt 2*evalQPoly rf1057.irrational a)/evalQPoly rf1057.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1057,rf1057]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (367/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-2411/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (2561/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-2935/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (24783/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-159/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (-6429/3128 : ℚ)*Polynomial.X^9 + Polynomial.C (496037/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-304429/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-233279/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (149/68 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1072.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1072.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1072.rational a+Real.sqrt 2*evalQPoly rf1072.irrational a)/evalQPoly rf1072.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1072,rf1057]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (79/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-677/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-842/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (22031/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-48031/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (233711/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-34330/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (533419/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-4479/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-1557/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1100.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1100.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1100.rational a+Real.sqrt 2*evalQPoly rf1100.irrational a)/evalQPoly rf1100.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1100,rf1057]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-67/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-32/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (947/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-264/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (8213/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-2336/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-53749/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (5860/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-109/92 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1142.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1142.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1142.rational a+Real.sqrt 2*evalQPoly rf1142.irrational a)/evalQPoly rf1142.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1142,rf1057]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (111/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (122/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2503/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (31573/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-112257/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (119368/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-14589/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (-3208/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (930803/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-209142/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-8113/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (37865/5474 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1085.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1085.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1085.rational a+Real.sqrt 2*evalQPoly rf1085.irrational a)/evalQPoly rf1085.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1085,rf1057]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (1007/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-648/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (6523/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-11637/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (28031/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-99551/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-77933/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (129971/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (-981357/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (6677/1564 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1114.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1114.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1114.rational a+Real.sqrt 2*evalQPoly rf1114.irrational a)/evalQPoly rf1114.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1114,rf1057]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (199/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (1116/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-4147/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (40122/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-163473/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (1020/161 : ℚ)*Polynomial.X^8 + Polynomial.C (-1691/644 : ℚ)*Polynomial.X^9 + Polynomial.C (-8749/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (415/644 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1155.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1155.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1155.rational a+Real.sqrt 2*evalQPoly rf1155.irrational a)/evalQPoly rf1155.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1155,rf1057]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-551/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (6747/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-3559/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (4381/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-145863/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (459573/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-20269/2380 : ℚ)*Polynomial.X^9 + Polynomial.C (134961/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (62389/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-38547/10948 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1127.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1127.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1127.rational a+Real.sqrt 2*evalQPoly rf1127.irrational a)/evalQPoly rf1127.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1127,rf1057]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (27/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (96/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-163/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (8439/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-2163/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (-5458/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (65939/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-18807/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (1085/1564 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1169.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1169.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1169.rational a+Real.sqrt 2*evalQPoly rf1169.irrational a)/evalQPoly rf1169.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1169,rf1057]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^1 + Polynomial.C (26/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (10/391 : ℚ)*Polynomial.X^3 + Polynomial.C (-507/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (2143/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-37498/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (60086/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-21171/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (7863/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (268/161 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1197.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1197.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1197.rational a+Real.sqrt 2*evalQPoly rf1197.irrational a)/evalQPoly rf1197.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1197,rf1057]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (31/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-1577/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (3327/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-22613/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (15466/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (26127/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-165093/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (440907/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-817/595 : ℚ)*Polynomial.X^10 + Polynomial.C (-5191/1564 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1182.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1182.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1182.rational a+Real.sqrt 2*evalQPoly rf1182.irrational a)/evalQPoly rf1182.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1182,rf1057]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (31/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-192/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1367/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-2061/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (1359/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-86/595 : ℚ)*Polynomial.X^7 + Polynomial.C (-29301/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (20479/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-979/782 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1211.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1211.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1211.rational a+Real.sqrt 2*evalQPoly rf1211.irrational a)/evalQPoly rf1211.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1211,rf1057]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even026
