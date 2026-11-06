import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even046
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1317.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (13/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (21/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-941/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (10655/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (-42327/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (77872/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-264643/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-13241/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (11979/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (49153/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-90119/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (1811/7820 : ℚ)*Polynomial.X^14 + Polynomial.C (2615/5474 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1317.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1317.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1317.rational a+Real.sqrt 2*evalQPoly rf1317.irrational a)/evalQPoly rf1317.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1317,rf1317]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-59/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (1107/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-2909/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (7081/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-7683/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (359/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (24077/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-154389/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (379649/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-2243/952 : ℚ)*Polynomial.X^12 + Polynomial.C (-10881/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (71/34 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1336.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1336.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1336.rational a+Real.sqrt 2*evalQPoly rf1336.irrational a)/evalQPoly rf1336.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1336,rf1317]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/2380 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/161 : ℚ)*Polynomial.X^4 + Polynomial.C (4211/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-10401/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (12051/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-55934/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (261859/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-15315/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (-18489/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (8532/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (134/161 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1372.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1372.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1372.rational a+Real.sqrt 2*evalQPoly rf1372.irrational a)/evalQPoly rf1372.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1372,rf1317]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-67/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-32/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (947/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-264/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (8213/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-2336/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-53749/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (5860/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-109/92 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1426.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1426.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1426.rational a+Real.sqrt 2*evalQPoly rf1426.irrational a)/evalQPoly rf1426.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1426,rf1317]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (19/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-87/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/1564 : ℚ)*Polynomial.X^3 + Polynomial.C (579/3220 : ℚ)*Polynomial.X^4 + Polynomial.C (-3789/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (158359/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-26917/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (187293/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (32689/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-735633/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (757899/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-11401/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (-115917/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (38861/10948 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1353.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1353.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1353.rational a+Real.sqrt 2*evalQPoly rf1353.irrational a)/evalQPoly rf1353.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1353,rf1317]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (11/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (3/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-757/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (453/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-5837/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (1115/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (-19/2380 : ℚ)*Polynomial.X^7 + Polynomial.C (8039/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-131993/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-59837/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (34553/4760 : ℚ)*Polynomial.X^11 + Polynomial.C (-44403/3910 : ℚ)*Polynomial.X^12 + Polynomial.C (2135/391 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1390.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1390.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1390.rational a+Real.sqrt 2*evalQPoly rf1390.irrational a)/evalQPoly rf1390.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1390,rf1317]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (9/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (393/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-4479/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1461/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-51473/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (303/115 : ℚ)*Polynomial.X^7 + Polynomial.C (-15599/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (-31053/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (10677/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (25909/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-178/161 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1443.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1443.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1443.rational a+Real.sqrt 2*evalQPoly rf1443.irrational a)/evalQPoly rf1443.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1443,rf1317]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-111/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (1969/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-28111/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (9006/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-4953/782 : ℚ)*Polynomial.X^8 + Polynomial.C (367177/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-98487/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-58462/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (222913/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (4279/10948 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1407.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1407.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1407.rational a+Real.sqrt 2*evalQPoly rf1407.irrational a)/evalQPoly rf1407.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1407,rf1317]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (523/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-103/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (18/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-86/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-123/238 : ℚ)*Polynomial.X^8 + Polynomial.C (4499/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-249/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (7421/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-939/1564 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1461.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1461.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1461.rational a+Real.sqrt 2*evalQPoly rf1461.irrational a)/evalQPoly rf1461.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1461,rf1317]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (81/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (114/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-7292/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (26969/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-9669/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (5790/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (30431/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-83961/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (53/322 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1497.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1497.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1497.rational a+Real.sqrt 2*evalQPoly rf1497.irrational a)/evalQPoly rf1497.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1497,rf1317]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (39/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (407/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-1933/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (7232/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-3031/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (-2017/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (244617/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-880/161 : ℚ)*Polynomial.X^9 + Polynomial.C (-7489/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (140827/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-905/782 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1478.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1478.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1478.rational a+Real.sqrt 2*evalQPoly rf1478.irrational a)/evalQPoly rf1478.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1478,rf1317]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (177/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-209/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (213/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (410/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-3912/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-12091/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (699/3220 : ℚ)*Polynomial.X^9 + Polynomial.C (16049/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-409/391 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1515.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1515.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1515.rational a+Real.sqrt 2*evalQPoly rf1515.irrational a)/evalQPoly rf1515.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1515,rf1317]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even046
