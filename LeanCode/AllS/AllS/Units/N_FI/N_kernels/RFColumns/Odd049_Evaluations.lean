import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd049
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1933.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (3/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-69/70 : ℚ)*Polynomial.X^4 + Polynomial.C (271/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-1251/70 : ℚ)*Polynomial.X^6 + Polynomial.C (169/14 : ℚ)*Polynomial.X^7 + Polynomial.C (941/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-1931/140 : ℚ)*Polynomial.X^9 + Polynomial.C (-699/70 : ℚ)*Polynomial.X^10 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1933.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1933.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1933.rational a+Real.sqrt 2*evalQPoly rf1933.irrational a)/evalQPoly rf1933.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1933,rf1933]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (3/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-89/70 : ℚ)*Polynomial.X^3 + Polynomial.C (26/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-351/70 : ℚ)*Polynomial.X^5 + Polynomial.C (34/35 : ℚ)*Polynomial.X^6 + Polynomial.C (253/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-4/5 : ℚ)*Polynomial.X^8 + Polynomial.C (-6/5 : ℚ)*Polynomial.X^9 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1952.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1952.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1952.rational a+Real.sqrt 2*evalQPoly rf1952.irrational a)/evalQPoly rf1952.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1952,rf1933]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (1/10 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^3 + Polynomial.C (61/70 : ℚ)*Polynomial.X^4 + Polynomial.C (34/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-351/70 : ℚ)*Polynomial.X^6 + Polynomial.C (187/70 : ℚ)*Polynomial.X^7 + Polynomial.C (267/70 : ℚ)*Polynomial.X^8 + Polynomial.C (3/4 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1989.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1989.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1989.rational a+Real.sqrt 2*evalQPoly rf1989.irrational a)/evalQPoly rf1989.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1989,rf1933]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^1 + Polynomial.C (5/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/14 : ℚ)*Polynomial.X^3 + Polynomial.C (51/35 : ℚ)*Polynomial.X^4 + Polynomial.C (653/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-2291/70 : ℚ)*Polynomial.X^6 + Polynomial.C (2873/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-121/28 : ℚ)*Polynomial.X^8 + Polynomial.C (-1917/70 : ℚ)*Polynomial.X^9 + Polynomial.C (-59/14 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1970.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1970.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1970.rational a+Real.sqrt 2*evalQPoly rf1970.irrational a)/evalQPoly rf1970.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1970,rf1933]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (2/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-26/35 : ℚ)*Polynomial.X^3 + Polynomial.C (128/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-58/7 : ℚ)*Polynomial.X^5 + Polynomial.C (50/7 : ℚ)*Polynomial.X^6 + Polynomial.C (74/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-108/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf2007.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2007.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2007.rational a+Real.sqrt 2*evalQPoly rf2007.irrational a)/evalQPoly rf2007.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2007,rf1933]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/70 : ℚ)*Polynomial.X^2 + Polynomial.C (9/14 : ℚ)*Polynomial.X^3 + Polynomial.C (9/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-303/70 : ℚ)*Polynomial.X^5 + Polynomial.C (137/70 : ℚ)*Polynomial.X^6 + Polynomial.C (331/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf2044.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2044.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2044.rational a+Real.sqrt 2*evalQPoly rf2044.irrational a)/evalQPoly rf2044.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2044,rf1933]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^3 + Polynomial.C (39/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-324/35 : ℚ)*Polynomial.X^5 + Polynomial.C (851/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-39/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-69/10 : ℚ)*Polynomial.X^8 + Polynomial.C (-45/28 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf2025.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2025.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2025.rational a+Real.sqrt 2*evalQPoly rf2025.irrational a)/evalQPoly rf2025.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2025,rf1933]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (59/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-261/70 : ℚ)*Polynomial.X^4 + Polynomial.C (17/5 : ℚ)*Polynomial.X^5 + Polynomial.C (1/14 : ℚ)*Polynomial.X^6 + Polynomial.C (29/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-27/14 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf2062.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2062.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2062.rational a+Real.sqrt 2*evalQPoly rf2062.irrational a)/evalQPoly rf2062.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2062,rf1933]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/70 : ℚ)*Polynomial.X^2 + Polynomial.C (9/14 : ℚ)*Polynomial.X^3 + Polynomial.C (9/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-303/70 : ℚ)*Polynomial.X^5 + Polynomial.C (137/70 : ℚ)*Polynomial.X^6 + Polynomial.C (331/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf2044.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2044.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2044.rational a+Real.sqrt 2*evalQPoly rf2044.irrational a)/evalQPoly rf2044.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2044,rf1933]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd049
