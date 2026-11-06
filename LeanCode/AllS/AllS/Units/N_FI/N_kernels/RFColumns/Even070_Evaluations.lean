import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even070
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1662.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/34 : ℚ)*Polynomial.X^2 + Polynomial.C (257/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-648/119 : ℚ)*Polynomial.X^4 + Polynomial.C (2592/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-7349/119 : ℚ)*Polynomial.X^6 + Polynomial.C (1957/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-13954/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-3117/119 : ℚ)*Polynomial.X^9 + Polynomial.C (8163/34 : ℚ)*Polynomial.X^10 + Polynomial.C (-43247/238 : ℚ)*Polynomial.X^11 + Polynomial.C (-1510/17 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1662.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1662.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1662.rational a+Real.sqrt 2*evalQPoly rf1662.irrational a)/evalQPoly rf1662.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1662,rf1662]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (6/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/17 : ℚ)*Polynomial.X^3 + Polynomial.C (691/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-2215/119 : ℚ)*Polynomial.X^5 + Polynomial.C (3027/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2603/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-16599/119 : ℚ)*Polynomial.X^8 + Polynomial.C (23875/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-5813/119 : ℚ)*Polynomial.X^10 + Polynomial.C (-2098/17 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1686.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1686.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1686.rational a+Real.sqrt 2*evalQPoly rf1686.irrational a)/evalQPoly rf1686.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1686,rf1662]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (233/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-352/119 : ℚ)*Polynomial.X^3 + Polynomial.C (2259/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-2586/119 : ℚ)*Polynomial.X^5 + Polynomial.C (685/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-6334/119 : ℚ)*Polynomial.X^7 + Polynomial.C (4377/238 : ℚ)*Polynomial.X^8 + Polynomial.C (10327/238 : ℚ)*Polynomial.X^9 + Polynomial.C (-59/4 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1732.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1732.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1732.rational a+Real.sqrt 2*evalQPoly rf1732.irrational a)/evalQPoly rf1732.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1732,rf1662]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^2 + Polynomial.C (29/119 : ℚ)*Polynomial.X^3 + Polynomial.C (5/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-499/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1023/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-241/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-439/17 : ℚ)*Polynomial.X^8 + Polynomial.C (49 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1801.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1801.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1801.rational a+Real.sqrt 2*evalQPoly rf1801.irrational a)/evalQPoly rf1801.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1801,rf1662]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (20/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-317/238 : ℚ)*Polynomial.X^2 + Polynomial.C (193/34 : ℚ)*Polynomial.X^3 + Polynomial.C (-1772/119 : ℚ)*Polynomial.X^4 + Polynomial.C (3310/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-5611/119 : ℚ)*Polynomial.X^6 + Polynomial.C (9001/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-10951/119 : ℚ)*Polynomial.X^8 + Polynomial.C (914/119 : ℚ)*Polynomial.X^9 + Polynomial.C (51579/238 : ℚ)*Polynomial.X^10 + Polynomial.C (-10743/34 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf1708.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1708.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1708.rational a+Real.sqrt 2*evalQPoly rf1708.irrational a)/evalQPoly rf1708.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1708,rf1662]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-94/119 : ℚ)*Polynomial.X^3 + Polynomial.C (856/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-3538/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1006/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-2370/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-21656/119 : ℚ)*Polynomial.X^8 + Polynomial.C (414 : ℚ)*Polynomial.X^9 + Polynomial.C (-5971/17 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf1755.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1755.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1755.rational a+Real.sqrt 2*evalQPoly rf1755.irrational a)/evalQPoly rf1755.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1755,rf1662]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^1 + Polynomial.C (354/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-937/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1067/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-290/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1478/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-1045/17 : ℚ)*Polynomial.X^7 + Polynomial.C (17683/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-27/2 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1823.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1823.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1823.rational a+Real.sqrt 2*evalQPoly rf1823.irrational a)/evalQPoly rf1823.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1823,rf1662]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-5/238 : ℚ)*Polynomial.X^0 + Polynomial.C (87/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-271/119 : ℚ)*Polynomial.X^2 + Polynomial.C (768/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-741/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-2005/119 : ℚ)*Polynomial.X^5 + Polynomial.C (78 : ℚ)*Polynomial.X^6 + Polynomial.C (-20260/119 : ℚ)*Polynomial.X^7 + Polynomial.C (57895/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-5939/34 : ℚ)*Polynomial.X^9 + Polynomial.C (1303/17 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf1777.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1777.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1777.rational a+Real.sqrt 2*evalQPoly rf1777.irrational a)/evalQPoly rf1777.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1777,rf1662]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/119 : ℚ)*Polynomial.X^2 + Polynomial.C (145/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-741/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1405/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-27/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-5037/119 : ℚ)*Polynomial.X^7 + Polynomial.C (1391/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-343/17 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf1846.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1846.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1846.rational a+Real.sqrt 2*evalQPoly rf1846.irrational a)/evalQPoly rf1846.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1846,rf1662]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (3/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-12/17 : ℚ)*Polynomial.X^1 + Polynomial.C (125/34 : ℚ)*Polynomial.X^2 + Polynomial.C (-771/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-795/119 : ℚ)*Polynomial.X^4 + Polynomial.C (862/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-23503/238 : ℚ)*Polynomial.X^6 + Polynomial.C (11125/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-167/4 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf1892.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1892.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1892.rational a+Real.sqrt 2*evalQPoly rf1892.irrational a)/evalQPoly rf1892.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1892,rf1662]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-3/238 : ℚ)*Polynomial.X^0 + Polynomial.C (47/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-108/119 : ℚ)*Polynomial.X^2 + Polynomial.C (52/119 : ℚ)*Polynomial.X^3 + Polynomial.C (893/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-2617/119 : ℚ)*Polynomial.X^5 + Polynomial.C (2064/119 : ℚ)*Polynomial.X^6 + Polynomial.C (3896/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-3081/34 : ℚ)*Polynomial.X^8 + Polynomial.C (4221/34 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf1868.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1868.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1868.rational a+Real.sqrt 2*evalQPoly rf1868.irrational a)/evalQPoly rf1868.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1868,rf1662]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/119 : ℚ)*Polynomial.X^2 + Polynomial.C (20/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-810/119 : ℚ)*Polynomial.X^4 + Polynomial.C (216/17 : ℚ)*Polynomial.X^5 + Polynomial.C (230/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-5492/119 : ℚ)*Polynomial.X^7 + Polynomial.C (1510/17 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf1915.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1915.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1915.rational a+Real.sqrt 2*evalQPoly rf1915.irrational a)/evalQPoly rf1915.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1915,rf1662]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even070
