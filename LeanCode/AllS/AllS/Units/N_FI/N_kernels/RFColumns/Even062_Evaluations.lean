import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even062
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1654.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (39/136 : ℚ)*Polynomial.X^1 + Polynomial.C (-2689/476 : ℚ)*Polynomial.X^2 + Polynomial.C (44179/952 : ℚ)*Polynomial.X^3 + Polynomial.C (-109339/476 : ℚ)*Polynomial.X^4 + Polynomial.C (3235/4 : ℚ)*Polynomial.X^5 + Polynomial.C (-474441/238 : ℚ)*Polynomial.X^6 + Polynomial.C (1441827/476 : ℚ)*Polynomial.X^7 + Polynomial.C (-62153/34 : ℚ)*Polynomial.X^8 + Polynomial.C (-1867595/952 : ℚ)*Polynomial.X^9 + Polynomial.C (2003683/476 : ℚ)*Polynomial.X^10 + Polynomial.C (-1822249/952 : ℚ)*Polynomial.X^11 + Polynomial.C (-76497/68 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1654.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1654.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1654.rational a+Real.sqrt 2*evalQPoly rf1654.irrational a)/evalQPoly rf1654.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1654,rf1654]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (2/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-265/119 : ℚ)*Polynomial.X^1 + Polynomial.C (2083/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-9578/119 : ℚ)*Polynomial.X^3 + Polynomial.C (28096/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-44790/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-366/7 : ℚ)*Polynomial.X^6 + Polynomial.C (28088/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-391222/119 : ℚ)*Polynomial.X^8 + Polynomial.C (283495/119 : ℚ)*Polynomial.X^9 + Polynomial.C (51347/119 : ℚ)*Polynomial.X^10 + Polynomial.C (-26186/17 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1678.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1678.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1678.rational a+Real.sqrt 2*evalQPoly rf1678.irrational a)/evalQPoly rf1678.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1678,rf1654]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (8/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-200/119 : ℚ)*Polynomial.X^1 + Polynomial.C (2076/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-11868/119 : ℚ)*Polynomial.X^3 + Polynomial.C (42276/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-100764/119 : ℚ)*Polynomial.X^5 + Polynomial.C (146428/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-13836/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-27836/119 : ℚ)*Polynomial.X^8 + Polynomial.C (89108/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-184 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1724.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1724.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1724.rational a+Real.sqrt 2*evalQPoly rf1724.irrational a)/evalQPoly rf1724.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1724,rf1654]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (67/119 : ℚ)*Polynomial.X^1 + Polynomial.C (52/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-1844/119 : ℚ)*Polynomial.X^3 + Polynomial.C (7198/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-15366/119 : ℚ)*Polynomial.X^5 + Polynomial.C (4996/119 : ℚ)*Polynomial.X^6 + Polynomial.C (48604/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-13561/17 : ℚ)*Polynomial.X^8 + Polynomial.C (637 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1793.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1793.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1793.rational a+Real.sqrt 2*evalQPoly rf1793.irrational a)/evalQPoly rf1793.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1793,rf1654]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-7/136 : ℚ)*Polynomial.X^0 + Polynomial.C (151/136 : ℚ)*Polynomial.X^1 + Polynomial.C (-10373/952 : ℚ)*Polynomial.X^2 + Polynomial.C (60653/952 : ℚ)*Polynomial.X^3 + Polynomial.C (-125313/476 : ℚ)*Polynomial.X^4 + Polynomial.C (401169/476 : ℚ)*Polynomial.X^5 + Polynomial.C (-1002377/476 : ℚ)*Polynomial.X^6 + Polynomial.C (1717937/476 : ℚ)*Polynomial.X^7 + Polynomial.C (-184445/56 : ℚ)*Polynomial.X^8 + Polynomial.C (-449539/952 : ℚ)*Polynomial.X^9 + Polynomial.C (4164887/952 : ℚ)*Polynomial.X^10 + Polynomial.C (-546617/136 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf1700.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1700.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1700.rational a+Real.sqrt 2*evalQPoly rf1700.irrational a)/evalQPoly rf1700.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1700,rf1654]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-240/119 : ℚ)*Polynomial.X^1 + Polynomial.C (2547/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-832/7 : ℚ)*Polynomial.X^3 + Polynomial.C (49086/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-102880/119 : ℚ)*Polynomial.X^5 + Polynomial.C (73902/119 : ℚ)*Polynomial.X^6 + Polynomial.C (226624/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-747781/119 : ℚ)*Polynomial.X^8 + Polynomial.C (133040/17 : ℚ)*Polynomial.X^9 + Polynomial.C (-73815/17 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf1747.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1747.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1747.rational a+Real.sqrt 2*evalQPoly rf1747.irrational a)/evalQPoly rf1747.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1747,rf1654]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (2/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-290/119 : ℚ)*Polynomial.X^1 + Polynomial.C (2224/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-9328/119 : ℚ)*Polynomial.X^3 + Polynomial.C (33052/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-5732/7 : ℚ)*Polynomial.X^5 + Polynomial.C (190208/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-223840/119 : ℚ)*Polynomial.X^7 + Polynomial.C (7878/7 : ℚ)*Polynomial.X^8 + Polynomial.C (-102 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1815.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1815.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1815.rational a+Real.sqrt 2*evalQPoly rf1815.irrational a)/evalQPoly rf1815.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1815,rf1654]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-9/136 : ℚ)*Polynomial.X^0 + Polynomial.C (108/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-235/136 : ℚ)*Polynomial.X^2 + Polynomial.C (-2850/119 : ℚ)*Polynomial.X^3 + Polynomial.C (83525/476 : ℚ)*Polynomial.X^4 + Polynomial.C (-82410/119 : ℚ)*Polynomial.X^5 + Polynomial.C (842995/476 : ℚ)*Polynomial.X^6 + Polynomial.C (-343622/119 : ℚ)*Polynomial.X^7 + Polynomial.C (3095557/952 : ℚ)*Polynomial.X^8 + Polynomial.C (-261146/119 : ℚ)*Polynomial.X^9 + Polynomial.C (128593/136 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf1769.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1769.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1769.rational a+Real.sqrt 2*evalQPoly rf1769.irrational a)/evalQPoly rf1769.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1769,rf1654]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/17 : ℚ)*Polynomial.X^0 + Polynomial.C (379/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-364/17 : ℚ)*Polynomial.X^2 + Polynomial.C (9388/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-20598/119 : ℚ)*Polynomial.X^4 + Polynomial.C (12042/119 : ℚ)*Polynomial.X^5 + Polynomial.C (3484/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-8452/7 : ℚ)*Polynomial.X^7 + Polynomial.C (20229/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-4459/17 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf1838.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1838.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1838.rational a+Real.sqrt 2*evalQPoly rf1838.irrational a)/evalQPoly rf1838.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1838,rf1654]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (36/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-1180/119 : ℚ)*Polynomial.X^2 + Polynomial.C (11604/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-47276/119 : ℚ)*Polynomial.X^4 + Polynomial.C (107180/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-150292/119 : ℚ)*Polynomial.X^6 + Polynomial.C (121052/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-380 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf1884.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1884.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1884.rational a+Real.sqrt 2*evalQPoly rf1884.irrational a)/evalQPoly rf1884.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1884,rf1654]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (75/476 : ℚ)*Polynomial.X^1 + Polynomial.C (47/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-3897/119 : ℚ)*Polynomial.X^3 + Polynomial.C (30455/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-59555/238 : ℚ)*Polynomial.X^5 + Polynomial.C (13925/119 : ℚ)*Polynomial.X^6 + Polynomial.C (98163/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-117673/68 : ℚ)*Polynomial.X^8 + Polynomial.C (108437/68 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf1860.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1860.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1860.rational a+Real.sqrt 2*evalQPoly rf1860.irrational a)/evalQPoly rf1860.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1860,rf1654]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-2/17 : ℚ)*Polynomial.X^0 + Polynomial.C (368/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-392/17 : ℚ)*Polynomial.X^2 + Polynomial.C (10032/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-21348/119 : ℚ)*Polynomial.X^4 + Polynomial.C (10448/119 : ℚ)*Polynomial.X^5 + Polynomial.C (70696/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-148080/119 : ℚ)*Polynomial.X^7 + Polynomial.C (18542/17 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf1907.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1907.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1907.rational a+Real.sqrt 2*evalQPoly rf1907.irrational a)/evalQPoly rf1907.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1907,rf1654]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even062
