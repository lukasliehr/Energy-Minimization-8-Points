import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd021
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1228.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^2 + Polynomial.C (37/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-117/35 : ℚ)*Polynomial.X^4 + Polynomial.C (209/70 : ℚ)*Polynomial.X^5 + Polynomial.C (169/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-209/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-27/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-183/28 : ℚ)*Polynomial.X^9 + Polynomial.C (-108/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1228.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1228.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1228.rational a+Real.sqrt 2*evalQPoly rf1228.irrational a)/evalQPoly rf1228.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1228,rf1228]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/28 : ℚ)*Polynomial.X^1 + Polynomial.C (41/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/35 : ℚ)*Polynomial.X^3 + Polynomial.C (6/7 : ℚ)*Polynomial.X^4 + Polynomial.C (15/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-141/70 : ℚ)*Polynomial.X^6 + Polynomial.C (81/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-81/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-111/140 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1239.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1239.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1239.rational a+Real.sqrt 2*evalQPoly rf1239.irrational a)/evalQPoly rf1239.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1239,rf1228]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (3/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-101/70 : ℚ)*Polynomial.X^4 + Polynomial.C (1/5 : ℚ)*Polynomial.X^5 + Polynomial.C (54/35 : ℚ)*Polynomial.X^6 + Polynomial.C (81/35 : ℚ)*Polynomial.X^7 + Polynomial.C (3/4 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1259.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1259.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1259.rational a+Real.sqrt 2*evalQPoly rf1259.irrational a)/evalQPoly rf1259.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1259,rf1228]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (12/35 : ℚ)*Polynomial.X^2 + Polynomial.C (3/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-327/70 : ℚ)*Polynomial.X^4 + Polynomial.C (323/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-857/70 : ℚ)*Polynomial.X^7 + Polynomial.C (17/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-1623/140 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1248.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1248.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1248.rational a+Real.sqrt 2*evalQPoly rf1248.irrational a)/evalQPoly rf1248.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1248,rf1228]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (37/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-149/70 : ℚ)*Polynomial.X^3 + Polynomial.C (179/70 : ℚ)*Polynomial.X^4 + Polynomial.C (123/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-57/14 : ℚ)*Polynomial.X^6 + Polynomial.C (57/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-187/70 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf1268.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1268.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1268.rational a+Real.sqrt 2*evalQPoly rf1268.irrational a)/evalQPoly rf1268.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1268,rf1228]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/10 : ℚ)*Polynomial.X^2 + Polynomial.C (-24/35 : ℚ)*Polynomial.X^3 + Polynomial.C (25/14 : ℚ)*Polynomial.X^4 + Polynomial.C (37/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-23/70 : ℚ)*Polynomial.X^6 + Polynomial.C (2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf1287.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1287.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1287.rational a+Real.sqrt 2*evalQPoly rf1287.irrational a)/evalQPoly rf1287.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1287,rf1228]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/14 : ℚ)*Polynomial.X^3 + Polynomial.C (27/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-149/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-99/70 : ℚ)*Polynomial.X^6 + Polynomial.C (117/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-619/140 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1278.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1278.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1278.rational a+Real.sqrt 2*evalQPoly rf1278.irrational a)/evalQPoly rf1278.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1278,rf1228]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (13/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/70 : ℚ)*Polynomial.X^2 + Polynomial.C (51/70 : ℚ)*Polynomial.X^3 + Polynomial.C (69/70 : ℚ)*Polynomial.X^4 + Polynomial.C (19/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-127/70 : ℚ)*Polynomial.X^6 + Polynomial.C (29/70 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf1297.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1297.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1297.rational a+Real.sqrt 2*evalQPoly rf1297.irrational a)/evalQPoly rf1297.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1297,rf1228]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (1/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-53/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^4 + Polynomial.C (221/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-13/35 : ℚ)*Polynomial.X^6 + Polynomial.C (3/2 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1307.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1307.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1307.rational a+Real.sqrt 2*evalQPoly rf1307.irrational a)/evalQPoly rf1307.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1307,rf1228]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd021
