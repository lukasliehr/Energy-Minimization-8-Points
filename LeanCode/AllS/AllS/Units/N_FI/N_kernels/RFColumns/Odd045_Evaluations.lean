import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd045
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1929.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (11/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-2017/140 : ℚ)*Polynomial.X^4 + Polynomial.C (2523/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-7429/35 : ℚ)*Polynomial.X^6 + Polynomial.C (12539/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-19203/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-2591/35 : ℚ)*Polynomial.X^9 + Polynomial.C (18623/70 : ℚ)*Polynomial.X^10 + Polynomial.C (-2934/35 : ℚ)*Polynomial.X^11 + Polynomial.C (-1439/20 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1929.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1929.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1929.rational a+Real.sqrt 2*evalQPoly rf1929.irrational a)/evalQPoly rf1929.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1929,rf1929]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-51/280 : ℚ)*Polynomial.X^1 + Polynomial.C (277/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-3333/280 : ℚ)*Polynomial.X^3 + Polynomial.C (304/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-2745/28 : ℚ)*Polynomial.X^5 + Polynomial.C (914/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-11471/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-1689/140 : ℚ)*Polynomial.X^8 + Polynomial.C (12413/280 : ℚ)*Polynomial.X^9 + Polynomial.C (-1221/140 : ℚ)*Polynomial.X^10 + Polynomial.C (-299/40 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1948.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1948.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1948.rational a+Real.sqrt 2*evalQPoly rf1948.irrational a)/evalQPoly rf1948.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1948,rf1929]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-23/140 : ℚ)*Polynomial.X^1 + Polynomial.C (43/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-258/35 : ℚ)*Polynomial.X^3 + Polynomial.C (251/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-817/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-3299/70 : ℚ)*Polynomial.X^6 + Polynomial.C (4366/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-15471/140 : ℚ)*Polynomial.X^8 + Polynomial.C (207/20 : ℚ)*Polynomial.X^9 + Polynomial.C (133/4 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1985.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1985.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1985.rational a+Real.sqrt 2*evalQPoly rf1985.irrational a)/evalQPoly rf1985.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1985,rf1929]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/56 : ℚ)*Polynomial.X^0 + Polynomial.C (-103/280 : ℚ)*Polynomial.X^1 + Polynomial.C (897/280 : ℚ)*Polynomial.X^2 + Polynomial.C (-4163/280 : ℚ)*Polynomial.X^3 + Polynomial.C (4847/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-307/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-33129/140 : ℚ)*Polynomial.X^6 + Polynomial.C (101313/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-290707/280 : ℚ)*Polynomial.X^8 + Polynomial.C (185373/280 : ℚ)*Polynomial.X^9 + Polynomial.C (8769/280 : ℚ)*Polynomial.X^10 + Polynomial.C (-8697/40 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1966.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1966.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1966.rational a+Real.sqrt 2*evalQPoly rf1966.irrational a)/evalQPoly rf1966.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1966,rf1929]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (47/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-463/70 : ℚ)*Polynomial.X^3 + Polynomial.C (2467/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-7753/70 : ℚ)*Polynomial.X^5 + Polynomial.C (14563/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-15313/70 : ℚ)*Polynomial.X^7 + Polynomial.C (6509/70 : ℚ)*Polynomial.X^8 + Polynomial.C (2283/70 : ℚ)*Polynomial.X^9 + Polynomial.C (-167/5 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf2003.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2003.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2003.rational a+Real.sqrt 2*evalQPoly rf2003.irrational a)/evalQPoly rf2003.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2003,rf1929]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (9/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-129/70 : ℚ)*Polynomial.X^2 + Polynomial.C (45/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-127/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-298/35 : ℚ)*Polynomial.X^5 + Polynomial.C (3373/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-2039/35 : ℚ)*Polynomial.X^7 + Polynomial.C (64/5 : ℚ)*Polynomial.X^8 + Polynomial.C (21 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf2040.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2040.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2040.rational a+Real.sqrt 2*evalQPoly rf2040.irrational a)/evalQPoly rf2040.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2040,rf1929]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (17/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-33/70 : ℚ)*Polynomial.X^3 + Polynomial.C (717/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-3536/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1231/5 : ℚ)*Polynomial.X^6 + Polynomial.C (-22551/70 : ℚ)*Polynomial.X^7 + Polynomial.C (26477/140 : ℚ)*Polynomial.X^8 + Polynomial.C (2879/140 : ℚ)*Polynomial.X^9 + Polynomial.C (-1263/20 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf2021.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2021.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2021.rational a+Real.sqrt 2*evalQPoly rf2021.irrational a)/evalQPoly rf2021.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2021,rf1929]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (47/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/10 : ℚ)*Polynomial.X^2 + Polynomial.C (614/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-771/14 : ℚ)*Polynomial.X^4 + Polynomial.C (7243/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-7649/70 : ℚ)*Polynomial.X^6 + Polynomial.C (244/5 : ℚ)*Polynomial.X^7 + Polynomial.C (436/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-299/20 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf2058.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2058.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2058.rational a+Real.sqrt 2*evalQPoly rf2058.irrational a)/evalQPoly rf2058.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2058,rf1929]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (53/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/14 : ℚ)*Polynomial.X^2 + Polynomial.C (309/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-389/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-147/10 : ℚ)*Polynomial.X^5 + Polynomial.C (905/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-2439/35 : ℚ)*Polynomial.X^7 + Polynomial.C (323/28 : ℚ)*Polynomial.X^8 + Polynomial.C (95/4 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf2076.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2076.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2076.rational a+Real.sqrt 2*evalQPoly rf2076.irrational a)/evalQPoly rf2076.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2076,rf1929]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd045
