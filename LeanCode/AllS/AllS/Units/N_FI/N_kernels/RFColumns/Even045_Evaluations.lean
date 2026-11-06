import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even045
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1316.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/34 : ℚ)*Polynomial.X^2 + Polynomial.C (-118/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1474/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-6577/119 : ℚ)*Polynomial.X^5 + Polynomial.C (16453/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-22700/119 : ℚ)*Polynomial.X^7 + Polynomial.C (6362/119 : ℚ)*Polynomial.X^8 + Polynomial.C (53943/238 : ℚ)*Polynomial.X^9 + Polynomial.C (-49197/238 : ℚ)*Polynomial.X^10 + Polynomial.C (-1510/17 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1316.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1316.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1316.rational a+Real.sqrt 2*evalQPoly rf1316.irrational a)/evalQPoly rf1316.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1316,rf1316]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (6/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-15/17 : ℚ)*Polynomial.X^2 + Polynomial.C (691/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-2215/119 : ℚ)*Polynomial.X^4 + Polynomial.C (3027/119 : ℚ)*Polynomial.X^5 + Polynomial.C (2603/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-16599/119 : ℚ)*Polynomial.X^7 + Polynomial.C (23875/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-5813/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-2098/17 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1335.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1335.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1335.rational a+Real.sqrt 2*evalQPoly rf1335.irrational a)/evalQPoly rf1335.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1335,rf1316]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/119 : ℚ)*Polynomial.X^2 + Polynomial.C (761/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-2628/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1073/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-10317/119 : ℚ)*Polynomial.X^6 + Polynomial.C (451/14 : ℚ)*Polynomial.X^7 + Polynomial.C (5706/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-73/4 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1371.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1371.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1371.rational a+Real.sqrt 2*evalQPoly rf1371.irrational a)/evalQPoly rf1371.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1371,rf1316]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^1 + Polynomial.C (29/119 : ℚ)*Polynomial.X^2 + Polynomial.C (5/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-499/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1023/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-241/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-439/17 : ℚ)*Polynomial.X^7 + Polynomial.C (49 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1425.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1425.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1425.rational a+Real.sqrt 2*evalQPoly rf1425.irrational a)/evalQPoly rf1425.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1425,rf1316]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-3/238 : ℚ)*Polynomial.X^0 + Polynomial.C (26/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-311/238 : ℚ)*Polynomial.X^2 + Polynomial.C (40/17 : ℚ)*Polynomial.X^3 + Polynomial.C (161/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-7760/119 : ℚ)*Polynomial.X^5 + Polynomial.C (20627/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-31184/119 : ℚ)*Polynomial.X^7 + Polynomial.C (40309/238 : ℚ)*Polynomial.X^8 + Polynomial.C (17198/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-10777/34 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf1352.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1352.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1352.rational a+Real.sqrt 2*evalQPoly rf1352.irrational a)/evalQPoly rf1352.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1352,rf1316]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-94/119 : ℚ)*Polynomial.X^2 + Polynomial.C (856/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-3538/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1006/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-2370/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-21656/119 : ℚ)*Polynomial.X^7 + Polynomial.C (414 : ℚ)*Polynomial.X^8 + Polynomial.C (-5971/17 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf1389.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1389.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1389.rational a+Real.sqrt 2*evalQPoly rf1389.irrational a)/evalQPoly rf1389.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1389,rf1316]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (3/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-80/119 : ℚ)*Polynomial.X^1 + Polynomial.C (358/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-214/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-5095/238 : ℚ)*Polynomial.X^4 + Polynomial.C (9276/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-2336/17 : ℚ)*Polynomial.X^6 + Polynomial.C (13738/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-89/4 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1442.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1442.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1442.rational a+Real.sqrt 2*evalQPoly rf1442.irrational a)/evalQPoly rf1442.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1442,rf1316]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (111/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-304/119 : ℚ)*Polynomial.X^2 + Polynomial.C (122/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-1943/119 : ℚ)*Polynomial.X^4 + Polynomial.C (4325/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-76 : ℚ)*Polynomial.X^6 + Polynomial.C (15318/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-25923/238 : ℚ)*Polynomial.X^8 + Polynomial.C (2521/34 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf1406.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1406.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1406.rational a+Real.sqrt 2*evalQPoly rf1406.irrational a)/evalQPoly rf1406.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1406,rf1316]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/119 : ℚ)*Polynomial.X^1 + Polynomial.C (145/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-741/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1405/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-27/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-5037/119 : ℚ)*Polynomial.X^6 + Polynomial.C (1391/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-343/17 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1460.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1460.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1460.rational a+Real.sqrt 2*evalQPoly rf1460.irrational a)/evalQPoly rf1460.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1460,rf1316]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/34 : ℚ)*Polynomial.X^1 + Polynomial.C (552/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-2507/238 : ℚ)*Polynomial.X^3 + Polynomial.C (317/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-8719/238 : ℚ)*Polynomial.X^5 + Polynomial.C (5686/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-59/2 : ℚ)*Polynomial.X^7
theorem eval9 (a : ℝ) (h : rf1496.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1496.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1496.rational a+Real.sqrt 2*evalQPoly rf1496.irrational a)/evalQPoly rf1496.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1496,rf1316]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (30/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-132/119 : ℚ)*Polynomial.X^2 + Polynomial.C (226/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-540/119 : ℚ)*Polynomial.X^4 + Polynomial.C (1602/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-116/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-1006/17 : ℚ)*Polynomial.X^7 + Polynomial.C (2170/17 : ℚ)*Polynomial.X^8
theorem eval10 (a : ℝ) (h : rf1477.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1477.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1477.rational a+Real.sqrt 2*evalQPoly rf1477.irrational a)/evalQPoly rf1477.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1477,rf1316]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/119 : ℚ)*Polynomial.X^1 + Polynomial.C (20/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-810/119 : ℚ)*Polynomial.X^3 + Polynomial.C (216/17 : ℚ)*Polynomial.X^4 + Polynomial.C (230/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-5492/119 : ℚ)*Polynomial.X^6 + Polynomial.C (1510/17 : ℚ)*Polynomial.X^7
theorem eval11 (a : ℝ) (h : rf1514.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1514.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1514.rational a+Real.sqrt 2*evalQPoly rf1514.irrational a)/evalQPoly rf1514.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1514,rf1316]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even045
