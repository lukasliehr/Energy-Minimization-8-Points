import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even065
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1657.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (41/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (269/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-988/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (37071/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-20435/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (210099/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-267059/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (6989081/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-2640033/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (339231/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (707359/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-23040419/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (113917/920 : ℚ)*Polynomial.X^14 + Polynomial.C (2472209/54740 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1657.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1657.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1657.rational a+Real.sqrt 2*evalQPoly rf1657.irrational a)/evalQPoly rf1657.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1657,rf1657]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (36/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-417/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (13/595 : ℚ)*Polynomial.X^4 + Polynomial.C (603/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (243/391 : ℚ)*Polynomial.X^6 + Polynomial.C (-13553/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (176298/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-76703/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-569438/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (2555019/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-802453/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-18997/322 : ℚ)*Polynomial.X^13 + Polynomial.C (7841/85 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1681.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1681.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1681.rational a+Real.sqrt 2*evalQPoly rf1681.irrational a)/evalQPoly rf1681.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1681,rf1657]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/6440 : ℚ)*Polynomial.X^1 + Polynomial.C (-25/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (73/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (1697/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-140033/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (148983/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-4997/322 : ℚ)*Polynomial.X^7 + Polynomial.C (116859/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (-3372353/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-38359/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (3139609/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-19727/340 : ℚ)*Polynomial.X^12 + Polynomial.C (10445/1288 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1727.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1727.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1727.rational a+Real.sqrt 2*evalQPoly rf1727.irrational a)/evalQPoly rf1727.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1727,rf1657]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (3/391 : ℚ)*Polynomial.X^3 + Polynomial.C (638/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-7088/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (34694/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-106826/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (22432/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (17470/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-710127/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (1145689/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-6362/115 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1796.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1796.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1796.rational a+Real.sqrt 2*evalQPoly rf1796.irrational a)/evalQPoly rf1796.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1796,rf1657]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/21896 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/1288 : ℚ)*Polynomial.X^1 + Polynomial.C (13/6440 : ℚ)*Polynomial.X^2 + Polynomial.C (1171/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-6727/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (38435/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-367229/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (26802/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-257077/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (3828793/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-13842533/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (5759657/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-2000393/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (-12326163/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (19920997/109480 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1703.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1703.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1703.rational a+Real.sqrt 2*evalQPoly rf1703.irrational a)/evalQPoly rf1703.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1703,rf1657]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (5/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-24/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (199/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-12417/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (45363/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-218682/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (16448/391 : ℚ)*Polynomial.X^8 + Polynomial.C (-605431/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-244353/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (759438/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-1071571/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (904289/3910 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1750.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1750.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1750.rational a+Real.sqrt 2*evalQPoly rf1750.irrational a)/evalQPoly rf1750.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1750,rf1657]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/6440 : ℚ)*Polynomial.X^0 + Polynomial.C (129/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-15/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-1457/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (106203/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-499/170 : ℚ)*Polynomial.X^5 + Polynomial.C (13368/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-43209/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (415761/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-1898763/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (792187/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (429183/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-153007/6440 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1818.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1818.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1818.rational a+Real.sqrt 2*evalQPoly rf1818.irrational a)/evalQPoly rf1818.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1818,rf1657]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (9/2380 : ℚ)*Polynomial.X^2 + Polynomial.C (871/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-37297/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (67843/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-124317/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-1101/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (375897/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-4855267/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (1702271/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-4307/28 : ℚ)*Polynomial.X^11 + Polynomial.C (515921/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (-206389/13685 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1772.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1772.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1772.rational a+Real.sqrt 2*evalQPoly rf1772.irrational a)/evalQPoly rf1772.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1772,rf1657]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (149/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-307/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (4668/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-5546/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (1070/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-25546/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-27818/1955 : ℚ)*Polynomial.X^9 + Polynomial.C (781511/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-26941/391 : ℚ)*Polynomial.X^11 + Polynomial.C (38899/1955 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1841.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1841.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1841.rational a+Real.sqrt 2*evalQPoly rf1841.irrational a)/evalQPoly rf1841.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1841,rf1657]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (173/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-2033/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (15458/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-56663/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-38576/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (532579/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-554951/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (379591/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-13852/391 : ℚ)*Polynomial.X^10 + Polynomial.C (8835/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1887.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1887.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1887.rational a+Real.sqrt 2*evalQPoly rf1887.irrational a)/evalQPoly rf1887.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1887,rf1657]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/15640 : ℚ)*Polynomial.X^0 + Polynomial.C (-53/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (31/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (533/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-33877/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (517/782 : ℚ)*Polynomial.X^5 + Polynomial.C (-134/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-66239/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (148201/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-585657/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (779/230 : ℚ)*Polynomial.X^10 + Polynomial.C (9861/340 : ℚ)*Polynomial.X^11 + Polynomial.C (-834057/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1863.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1863.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1863.rational a+Real.sqrt 2*evalQPoly rf1863.irrational a)/evalQPoly rf1863.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1863,rf1657]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^2 + Polynomial.C (353/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-926/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1094/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-47013/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (17873/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-10202/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-60342/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (221059/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (-213633/3910 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1910.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1910.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1910.rational a+Real.sqrt 2*evalQPoly rf1910.irrational a)/evalQPoly rf1910.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1910,rf1657]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even065
