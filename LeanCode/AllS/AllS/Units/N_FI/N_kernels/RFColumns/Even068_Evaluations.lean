import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even068
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1660.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (3/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (74/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-6869/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (4817/15640 : ℚ)*Polynomial.X^6 + Polynomial.C (-10959/10948 : ℚ)*Polynomial.X^7 + Polynomial.C (36039/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-96879/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (1314221/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-8443/595 : ℚ)*Polynomial.X^11 + Polynomial.C (11551/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (2125309/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-1421011/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (-9413/1564 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1660.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1660.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1660.rational a+Real.sqrt 2*evalQPoly rf1660.irrational a)/evalQPoly rf1660.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1660,rf1660]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (263/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (249/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-297/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (233/322 : ℚ)*Polynomial.X^7 + Polynomial.C (-45557/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (35429/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (200547/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-683303/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (756019/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-4387/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-281/34 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1684.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1684.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1684.rational a+Real.sqrt 2*evalQPoly rf1684.irrational a)/evalQPoly rf1684.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1684,rf1660]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-183/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1636/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-6546/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (6995/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-1136/391 : ℚ)*Polynomial.X^8 + Polynomial.C (1831/340 : ℚ)*Polynomial.X^9 + Polynomial.C (-74626/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-23241/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (60311/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-33/46 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1730.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1730.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1730.rational a+Real.sqrt 2*evalQPoly rf1730.irrational a)/evalQPoly rf1730.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1730,rf1660]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (0 : ℚ)*Polynomial.X^5 + Polynomial.C (-29/1610 : ℚ)*Polynomial.X^6 + Polynomial.C (131/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-2521/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (1212/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (8383/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-90053/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (317/92 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1799.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1799.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1799.rational a+Real.sqrt 2*evalQPoly rf1799.irrational a)/evalQPoly rf1799.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1799,rf1660]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-67/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-93/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (8921/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-4181/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (15193/15640 : ℚ)*Polynomial.X^6 + Polynomial.C (-1122/805 : ℚ)*Polynomial.X^7 + Polynomial.C (141417/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-142257/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (57859/6440 : ℚ)*Polynomial.X^10 + Polynomial.C (-33891/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (1245183/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (739233/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-66389/3128 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1706.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1706.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1706.rational a+Real.sqrt 2*evalQPoly rf1706.irrational a)/evalQPoly rf1706.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1706,rf1660]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-79/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (2693/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-5777/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (11474/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-10269/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (242617/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1937/2380 : ℚ)*Polynomial.X^10 + Polynomial.C (-261612/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (274439/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (-36687/1564 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1753.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1753.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1753.rational a+Real.sqrt 2*evalQPoly rf1753.irrational a)/evalQPoly rf1753.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1753,rf1660]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (29/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (439/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-3639/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (38/85 : ℚ)*Polynomial.X^5 + Polynomial.C (-19087/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (361/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-6917/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (60034/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-453183/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (153743/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-4/23 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1821.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1821.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1821.rational a+Real.sqrt 2*evalQPoly rf1821.irrational a)/evalQPoly rf1821.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1821,rf1660]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-503/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (6983/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-15979/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-439/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (2683/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (-473027/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (780841/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-27588/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (592849/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-161191/21896 : ℚ)*Polynomial.X^12 + Polynomial.C (14481/3128 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1775.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1775.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1775.rational a+Real.sqrt 2*evalQPoly rf1775.irrational a)/evalQPoly rf1775.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1775,rf1660]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-47/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (228/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (1147/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-318/805 : ℚ)*Polynomial.X^7 + Polynomial.C (27367/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-1060/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-171477/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (70501/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-1943/1564 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1844.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1844.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1844.rational a+Real.sqrt 2*evalQPoly rf1844.irrational a)/evalQPoly rf1844.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1844,rf1660]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (141/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (-2521/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2377/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (793/1190 : ℚ)*Polynomial.X^6 + Polynomial.C (-71147/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (6635/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (-45233/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (29299/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-247/92 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1890.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1890.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1890.rational a+Real.sqrt 2*evalQPoly rf1890.irrational a)/evalQPoly rf1890.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1890,rf1660]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (13/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (534/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-339/1610 : ℚ)*Polynomial.X^6 + Polynomial.C (857/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-1483/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-2218/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (49057/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-29471/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (13131/1564 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1866.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1866.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1866.rational a+Real.sqrt 2*evalQPoly rf1866.irrational a)/evalQPoly rf1866.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1866,rf1660]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (50/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-1161/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (367/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (-111/391 : ℚ)*Polynomial.X^7 + Polynomial.C (5618/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (10481/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-108257/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (4239/782 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1913.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1913.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1913.rational a+Real.sqrt 2*evalQPoly rf1913.irrational a)/evalQPoly rf1913.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1913,rf1660]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even068
