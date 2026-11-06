import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even071
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1663.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/5474 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/3128 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/1610 : ℚ)*Polynomial.X^4 + Polynomial.C (10687/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-30609/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (189787/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-4775/1564 : ℚ)*Polynomial.X^8 + Polynomial.C (286277/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (1696/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-49071/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (2911/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (171357/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-277177/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (69637/21896 : ℚ)*Polynomial.X^15 + Polynomial.C (14407/10948 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1663.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1663.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1663.rational a+Real.sqrt 2*evalQPoly rf1663.irrational a)/evalQPoly rf1663.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1663,rf1663]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (13/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-171/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (2997/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-1655/10948 : ℚ)*Polynomial.X^6 + Polynomial.C (4007/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (29289/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-114029/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (957/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (103251/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (100389/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-45159/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-1287/805 : ℚ)*Polynomial.X^14 + Polynomial.C (32/17 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1687.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1687.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1687.rational a+Real.sqrt 2*evalQPoly rf1687.irrational a)/evalQPoly rf1687.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1687,rf1663]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-129/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-767/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (17729/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-19904/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (18259/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-45229/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-12774/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (52459/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (7/68 : ℚ)*Polynomial.X^12 + Polynomial.C (-69903/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (53/644 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1733.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1733.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1733.rational a+Real.sqrt 2*evalQPoly rf1733.irrational a)/evalQPoly rf1733.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1733,rf1663]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-67/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-32/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (947/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-264/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (8213/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-2336/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-53749/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (5860/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-109/92 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1802.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1802.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1802.rational a+Real.sqrt 2*evalQPoly rf1802.irrational a)/evalQPoly rf1802.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1802,rf1663]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (89/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (653/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-9997/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (54769/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-163157/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (52225/21896 : ℚ)*Polynomial.X^7 + Polynomial.C (-121361/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-293977/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (478759/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-123377/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-165027/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (160603/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-25531/6440 : ℚ)*Polynomial.X^14 + Polynomial.C (97203/21896 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1709.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1709.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1709.rational a+Real.sqrt 2*evalQPoly rf1709.irrational a)/evalQPoly rf1709.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1709,rf1663]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (771/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-719/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (107/644 : ℚ)*Polynomial.X^5 + Polynomial.C (-9663/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-22269/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (164049/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-24685/21896 : ℚ)*Polynomial.X^9 + Polynomial.C (-13981/6440 : ℚ)*Polynomial.X^10 + Polynomial.C (417591/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (117571/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-3340/391 : ℚ)*Polynomial.X^13 + Polynomial.C (3787/782 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1756.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1756.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1756.rational a+Real.sqrt 2*evalQPoly rf1756.irrational a)/evalQPoly rf1756.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1756,rf1663]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (67/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (369/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-905/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (93/115 : ℚ)*Polynomial.X^6 + Polynomial.C (-59261/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (8277/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-8197/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-14073/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (33115/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-263/322 : ℚ)*Polynomial.X^12 + Polynomial.C (-17/161 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1824.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1824.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1824.rational a+Real.sqrt 2*evalQPoly rf1824.irrational a)/evalQPoly rf1824.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1824,rf1663]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-383/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (8907/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-1467/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (15401/15640 : ℚ)*Polynomial.X^6 + Polynomial.C (-2081/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (280829/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-142731/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-9419/6440 : ℚ)*Polynomial.X^10 + Polynomial.C (473997/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-944103/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (37607/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-30887/21896 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1778.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1778.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1778.rational a+Real.sqrt 2*evalQPoly rf1778.irrational a)/evalQPoly rf1778.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1778,rf1663]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (-11/805 : ℚ)*Polynomial.X^4 + Polynomial.C (173/2380 : ℚ)*Polynomial.X^5 + Polynomial.C (-3169/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-7419/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (2676/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-111/68 : ℚ)*Polynomial.X^9 + Polynomial.C (-75553/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (41947/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-541/115 : ℚ)*Polynomial.X^12 + Polynomial.C (2051/1564 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1847.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1847.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1847.rational a+Real.sqrt 2*evalQPoly rf1847.irrational a)/evalQPoly rf1847.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1847,rf1663]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (3/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (209/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-9053/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (9461/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-18918/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (10936/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (14137/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-84281/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (1691/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (5127/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-55/644 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1893.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1893.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1893.rational a+Real.sqrt 2*evalQPoly rf1893.irrational a)/evalQPoly rf1893.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1893,rf1663]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-869/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (7711/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-26177/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (7073/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (30063/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-198403/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (4119/1610 : ℚ)*Polynomial.X^9 + Polynomial.C (2343/1610 : ℚ)*Polynomial.X^10 + Polynomial.C (-42649/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-53931/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1695/1564 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1869.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1869.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1869.rational a+Real.sqrt 2*evalQPoly rf1869.irrational a)/evalQPoly rf1869.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1869,rf1663]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (1038/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-4609/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (36/805 : ℚ)*Polynomial.X^6 + Polynomial.C (6096/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-30561/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-4129/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-11398/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (8803/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-1669/782 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1916.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1916.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1916.rational a+Real.sqrt 2*evalQPoly rf1916.irrational a)/evalQPoly rf1916.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1916,rf1663]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even071
