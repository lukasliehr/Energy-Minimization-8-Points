import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even048
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1319.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/238 : ℚ)*Polynomial.X^1 + Polynomial.C (1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^3 + Polynomial.C (226/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-554/119 : ℚ)*Polynomial.X^5 + Polynomial.C (83/119 : ℚ)*Polynomial.X^6 + Polynomial.C (3011/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-5302/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-891/238 : ℚ)*Polynomial.X^9 + Polynomial.C (10609/238 : ℚ)*Polynomial.X^10 + Polynomial.C (797/119 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1319.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1319.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1319.rational a+Real.sqrt 2*evalQPoly rf1319.irrational a)/evalQPoly rf1319.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1319,rf1319]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/119 : ℚ)*Polynomial.X^2 + Polynomial.C (6/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-285/238 : ℚ)*Polynomial.X^4 + Polynomial.C (121/238 : ℚ)*Polynomial.X^5 + Polynomial.C (1311/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-916/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-2343/238 : ℚ)*Polynomial.X^8 + Polynomial.C (4149/476 : ℚ)*Polynomial.X^9 + Polynomial.C (857/34 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1338.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1338.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1338.rational a+Real.sqrt 2*evalQPoly rf1338.irrational a)/evalQPoly rf1338.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1338,rf1319]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/119 : ℚ)*Polynomial.X^2 + Polynomial.C (122/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-89/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-538/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1297/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-22/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-1787/119 : ℚ)*Polynomial.X^8 + Polynomial.C (24/7 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1374.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1374.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1374.rational a+Real.sqrt 2*evalQPoly rf1374.irrational a)/evalQPoly rf1374.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1374,rf1319]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (3/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-40/119 : ℚ)*Polynomial.X^3 + Polynomial.C (155/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-216/119 : ℚ)*Polynomial.X^5 + Polynomial.C (9/119 : ℚ)*Polynomial.X^6 + Polynomial.C (64/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-17 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1428.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1428.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1428.rational a+Real.sqrt 2*evalQPoly rf1428.irrational a)/evalQPoly rf1428.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1428,rf1319]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-10/119 : ℚ)*Polynomial.X^1 + Polynomial.C (151/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-292/119 : ℚ)*Polynomial.X^3 + Polynomial.C (90/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-664/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-80/17 : ℚ)*Polynomial.X^6 + Polynomial.C (4780/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-19381/238 : ℚ)*Polynomial.X^8 + Polynomial.C (5914/119 : ℚ)*Polynomial.X^9 + Polynomial.C (7825/238 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf1355.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1355.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1355.rational a+Real.sqrt 2*evalQPoly rf1355.irrational a)/evalQPoly rf1355.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1355,rf1319]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (11/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/119 : ℚ)*Polynomial.X^2 + Polynomial.C (25/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-33/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-95/34 : ℚ)*Polynomial.X^5 + Polynomial.C (201/17 : ℚ)*Polynomial.X^6 + Polynomial.C (-1089/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-2059/68 : ℚ)*Polynomial.X^8 + Polynomial.C (3969/68 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf1392.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1392.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1392.rational a+Real.sqrt 2*evalQPoly rf1392.irrational a)/evalQPoly rf1392.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1392,rf1319]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (32/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-169/119 : ℚ)*Polynomial.X^2 + Polynomial.C (48/17 : ℚ)*Polynomial.X^3 + Polynomial.C (11/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-1256/119 : ℚ)*Polynomial.X^5 + Polynomial.C (2325/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-1160/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-37/7 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1445.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1445.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1445.rational a+Real.sqrt 2*evalQPoly rf1445.irrational a)/evalQPoly rf1445.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1445,rf1319]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-7/34 : ℚ)*Polynomial.X^1 + Polynomial.C (8/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-305/119 : ℚ)*Polynomial.X^3 + Polynomial.C (99/119 : ℚ)*Polynomial.X^4 + Polynomial.C (838/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-196/17 : ℚ)*Polynomial.X^6 + Polynomial.C (705/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-2977/238 : ℚ)*Polynomial.X^8 + Polynomial.C (773/238 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf1409.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1409.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1409.rational a+Real.sqrt 2*evalQPoly rf1409.irrational a)/evalQPoly rf1409.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1409,rf1319]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/34 : ℚ)*Polynomial.X^1 + Polynomial.C (18/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-87/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-47/238 : ℚ)*Polynomial.X^4 + Polynomial.C (811/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-268/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-2061/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-45/68 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1463.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1463.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1463.rational a+Real.sqrt 2*evalQPoly rf1463.irrational a)/evalQPoly rf1463.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1463,rf1319]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/119 : ℚ)*Polynomial.X^0 + Polynomial.C (45/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-207/119 : ℚ)*Polynomial.X^2 + Polynomial.C (277/119 : ℚ)*Polynomial.X^3 + Polynomial.C (49/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-1297/119 : ℚ)*Polynomial.X^5 + Polynomial.C (1115/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^7
theorem eval9 (a : ℝ) (h : rf1499.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1499.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1499.rational a+Real.sqrt 2*evalQPoly rf1499.irrational a)/evalQPoly rf1499.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1499,rf1319]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/17 : ℚ)*Polynomial.X^1 + Polynomial.C (53/119 : ℚ)*Polynomial.X^2 + Polynomial.C (26/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-71/17 : ℚ)*Polynomial.X^4 + Polynomial.C (654/119 : ℚ)*Polynomial.X^5 + Polynomial.C (999/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-2458/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-116/17 : ℚ)*Polynomial.X^8
theorem eval10 (a : ℝ) (h : rf1480.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1480.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1480.rational a+Real.sqrt 2*evalQPoly rf1480.irrational a)/evalQPoly rf1480.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1480,rf1319]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/238 : ℚ)*Polynomial.X^1 + Polynomial.C (23/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/14 : ℚ)*Polynomial.X^4 + Polynomial.C (1009/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-415/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-575/34 : ℚ)*Polynomial.X^7
theorem eval11 (a : ℝ) (h : rf1517.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1517.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1517.rational a+Real.sqrt 2*evalQPoly rf1517.irrational a)/evalQPoly rf1517.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1517,rf1319]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even048
