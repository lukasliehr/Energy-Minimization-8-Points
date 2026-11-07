import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even075
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1667.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (3/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-37/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-389/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (14363/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-2159/3220 : ℚ)*Polynomial.X^7 + Polynomial.C (19902/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-1363/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (-482491/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (5825/782 : ℚ)*Polynomial.X^11 + Polynomial.C (-50039/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-52461/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (205601/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (91197/54740 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1667.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1667.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1667.rational a+Real.sqrt 2*evalQPoly rf1667.irrational a)/evalQPoly rf1667.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1667,rf1667]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (-39/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-963/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (2182/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-2977/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (15569/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (36543/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-230249/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (148377/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (130453/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-89499/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-319/170 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1691.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1691.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1691.rational a+Real.sqrt 2*evalQPoly rf1691.irrational a)/evalQPoly rf1691.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1691,rf1667]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-22/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (7453/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-88/391 : ℚ)*Polynomial.X^6 + Polynomial.C (1335/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (1236/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-145079/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (2798/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (13791/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-1478/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-1201/1288 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1737.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1737.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1737.rational a+Real.sqrt 2*evalQPoly rf1737.irrational a)/evalQPoly rf1737.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1737,rf1667]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (1/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-61/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-52/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (2197/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-3469/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-6751/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (223/230 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1806.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1806.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1806.rational a+Real.sqrt 2*evalQPoly rf1806.irrational a)/evalQPoly rf1806.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1806,rf1667]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-41/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (99/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (194/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-5637/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (22315/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (-413/170 : ℚ)*Polynomial.X^7 + Polynomial.C (24593/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (280877/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-73789/4760 : ℚ)*Polynomial.X^10 + Polynomial.C (38481/2380 : ℚ)*Polynomial.X^11 + Polynomial.C (-1209/391 : ℚ)*Polynomial.X^12 + Polynomial.C (-93589/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (439181/109480 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1713.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1713.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1713.rational a+Real.sqrt 2*evalQPoly rf1713.irrational a)/evalQPoly rf1713.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1713,rf1667]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (31/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (12/805 : ℚ)*Polynomial.X^4 + Polynomial.C (-263/1564 : ℚ)*Polynomial.X^5 + Polynomial.C (2020/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-21159/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (7823/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (262671/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-307943/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (245447/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (25289/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-42781/7820 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1760.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1760.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1760.rational a+Real.sqrt 2*evalQPoly rf1760.irrational a)/evalQPoly rf1760.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1760,rf1667]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (401/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-9351/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (10371/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-10159/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-1439/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (320323/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-242093/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (9111/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (171613/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-12141/6440 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1828.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1828.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1828.rational a+Real.sqrt 2*evalQPoly rf1828.irrational a)/evalQPoly rf1828.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1828,rf1667]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/1564 : ℚ)*Polynomial.X^3 + Polynomial.C (8927/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-1493/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (2755/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-39229/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-20467/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (350373/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-204919/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (785291/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-102251/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-73062/13685 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1782.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1782.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1782.rational a+Real.sqrt 2*evalQPoly rf1782.irrational a)/evalQPoly rf1782.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1782,rf1667]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (47/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (827/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-821/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (16503/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-31859/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (10547/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (26103/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-12335/1564 : ℚ)*Polynomial.X^10 + Polynomial.C (57729/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-16807/7820 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1851.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1851.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1851.rational a+Real.sqrt 2*evalQPoly rf1851.irrational a)/evalQPoly rf1851.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1851,rf1667]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (41/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (911/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-825/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (14137/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-3373/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-24651/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (207241/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-48541/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (3769/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (731/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1897.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1897.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1897.rational a+Real.sqrt 2*evalQPoly rf1897.irrational a)/evalQPoly rf1897.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1897,rf1667]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-531/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (5507/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-397/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-7748/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (40837/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (257/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-274077/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (157253/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (97721/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-69761/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1873.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1873.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1873.rational a+Real.sqrt 2*evalQPoly rf1873.irrational a)/evalQPoly rf1873.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1873,rf1667]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (1/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (403/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-6633/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (295/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (22637/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-81729/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (2986/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (4661/3910 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1920.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1920.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1920.rational a+Real.sqrt 2*evalQPoly rf1920.irrational a)/evalQPoly rf1920.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1920,rf1667]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even075
