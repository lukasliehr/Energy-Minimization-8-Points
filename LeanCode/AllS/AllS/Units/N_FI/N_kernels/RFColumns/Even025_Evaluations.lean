import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even025
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1056.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-260/119 : ℚ)*Polynomial.X^2 + Polynomial.C (1874/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-7122/119 : ℚ)*Polynomial.X^4 + Polynomial.C (16118/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-19858/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2214/119 : ℚ)*Polynomial.X^7 + Polynomial.C (29290/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-25084/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-1646/17 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1056.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1056.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1056.rational a+Real.sqrt 2*evalQPoly rf1056.irrational a)/evalQPoly rf1056.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1056,rf1056]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (6/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-15/17 : ℚ)*Polynomial.X^1 + Polynomial.C (691/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-2215/119 : ℚ)*Polynomial.X^3 + Polynomial.C (3027/119 : ℚ)*Polynomial.X^4 + Polynomial.C (2603/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-16599/119 : ℚ)*Polynomial.X^6 + Polynomial.C (23875/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-5813/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-2098/17 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1071.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1071.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1071.rational a+Real.sqrt 2*evalQPoly rf1071.irrational a)/evalQPoly rf1071.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1071,rf1056]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (4/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-86/119 : ℚ)*Polynomial.X^1 + Polynomial.C (1433/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-2985/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1913/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-8252/119 : ℚ)*Polynomial.X^5 + Polynomial.C (5063/238 : ℚ)*Polynomial.X^6 + Polynomial.C (5643/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-33/2 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1099.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1099.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1099.rational a+Real.sqrt 2*evalQPoly rf1099.irrational a)/evalQPoly rf1099.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1099,rf1056]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-3/119 : ℚ)*Polynomial.X^0 + Polynomial.C (29/119 : ℚ)*Polynomial.X^1 + Polynomial.C (5/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-499/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1023/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-241/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-439/17 : ℚ)*Polynomial.X^6 + Polynomial.C (49 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1141.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1141.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1141.rational a+Real.sqrt 2*evalQPoly rf1141.irrational a)/evalQPoly rf1141.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1141,rf1056]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (6/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-410/119 : ℚ)*Polynomial.X^2 + Polynomial.C (134/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-7862/119 : ℚ)*Polynomial.X^4 + Polynomial.C (17362/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-23966/119 : ℚ)*Polynomial.X^6 + Polynomial.C (11362/119 : ℚ)*Polynomial.X^7 + Polynomial.C (23280/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-5788/17 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1084.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1084.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1084.rational a+Real.sqrt 2*evalQPoly rf1084.irrational a)/evalQPoly rf1084.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1084,rf1056]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-94/119 : ℚ)*Polynomial.X^1 + Polynomial.C (856/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-3538/119 : ℚ)*Polynomial.X^3 + Polynomial.C (1006/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-2370/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-21656/119 : ℚ)*Polynomial.X^6 + Polynomial.C (414 : ℚ)*Polynomial.X^7 + Polynomial.C (-5971/17 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1113.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1113.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1113.rational a+Real.sqrt 2*evalQPoly rf1113.irrational a)/evalQPoly rf1113.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1113,rf1056]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (4/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-83/119 : ℚ)*Polynomial.X^1 + Polynomial.C (626/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-2369/119 : ℚ)*Polynomial.X^3 + Polynomial.C (6336/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-1715/17 : ℚ)*Polynomial.X^5 + Polynomial.C (650/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-17 : ℚ)*Polynomial.X^7
theorem eval6 (a : ℝ) (h : rf1154.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1154.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1154.rational a+Real.sqrt 2*evalQPoly rf1154.irrational a)/evalQPoly rf1154.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1154,rf1056]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (16/119 : ℚ)*Polynomial.X^1 + Polynomial.C (124/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-1504/119 : ℚ)*Polynomial.X^3 + Polynomial.C (328/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-13008/119 : ℚ)*Polynomial.X^5 + Polynomial.C (20900/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-992/7 : ℚ)*Polynomial.X^7 + Polynomial.C (1558/17 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1126.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1126.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1126.rational a+Real.sqrt 2*evalQPoly rf1126.irrational a)/evalQPoly rf1126.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1126,rf1056]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-9/119 : ℚ)*Polynomial.X^0 + Polynomial.C (145/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-741/119 : ℚ)*Polynomial.X^2 + Polynomial.C (1405/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-5037/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1391/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-343/17 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1168.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1168.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1168.rational a+Real.sqrt 2*evalQPoly rf1168.irrational a)/evalQPoly rf1168.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1168,rf1056]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (69/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-1233/238 : ℚ)*Polynomial.X^2 + Polynomial.C (26 : ℚ)*Polynomial.X^3 + Polynomial.C (-14809/238 : ℚ)*Polynomial.X^4 + Polynomial.C (8437/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-73/2 : ℚ)*Polynomial.X^6
theorem eval9 (a : ℝ) (h : rf1196.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1196.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1196.rational a+Real.sqrt 2*evalQPoly rf1196.irrational a)/evalQPoly rf1196.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1196,rf1056]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/119 : ℚ)*Polynomial.X^1 + Polynomial.C (32/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-1368/119 : ℚ)*Polynomial.X^3 + Polynomial.C (2496/119 : ℚ)*Polynomial.X^4 + Polynomial.C (776/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-1248/17 : ℚ)*Polynomial.X^6 + Polynomial.C (2408/17 : ℚ)*Polynomial.X^7
theorem eval10 (a : ℝ) (h : rf1181.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1181.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1181.rational a+Real.sqrt 2*evalQPoly rf1181.irrational a)/evalQPoly rf1181.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1181,rf1056]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-6/119 : ℚ)*Polynomial.X^0 + Polynomial.C (20/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-810/119 : ℚ)*Polynomial.X^2 + Polynomial.C (216/17 : ℚ)*Polynomial.X^3 + Polynomial.C (230/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-5492/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1510/17 : ℚ)*Polynomial.X^6
theorem eval11 (a : ℝ) (h : rf1210.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1210.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1210.rational a+Real.sqrt 2*evalQPoly rf1210.irrational a)/evalQPoly rf1210.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1210,rf1056]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even025
