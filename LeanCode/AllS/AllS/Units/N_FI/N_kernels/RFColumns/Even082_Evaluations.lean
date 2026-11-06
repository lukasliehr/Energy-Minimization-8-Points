import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even082
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1673.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (7/8 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/4 : ℚ)*Polynomial.X^2 + Polynomial.C (275/8 : ℚ)*Polynomial.X^3 + Polynomial.C (-319/4 : ℚ)*Polynomial.X^4 + Polynomial.C (821/8 : ℚ)*Polynomial.X^5 + Polynomial.C (-235/4 : ℚ)*Polynomial.X^6 + Polynomial.C (-47/8 : ℚ)*Polynomial.X^7 + Polynomial.C (71/4 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1673.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1673.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1673.rational a+Real.sqrt 2*evalQPoly rf1673.irrational a)/evalQPoly rf1673.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1673,rf1673]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := 0
theorem eval1 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf0013,rf1673]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := 0
theorem eval2 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf0013,rf1673]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := 0
theorem eval3 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf0013,rf1673]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-7/8 : ℚ)*Polynomial.X^0 + Polynomial.C (67/8 : ℚ)*Polynomial.X^1 + Polynomial.C (-309/8 : ℚ)*Polynomial.X^2 + Polynomial.C (873/8 : ℚ)*Polynomial.X^3 + Polynomial.C (-1601/8 : ℚ)*Polynomial.X^4 + Polynomial.C (1877/8 : ℚ)*Polynomial.X^5 + Polynomial.C (-1299/8 : ℚ)*Polynomial.X^6 + Polynomial.C (399/8 : ℚ)*Polynomial.X^7
theorem eval4 (a : ℝ) (h : rf1719.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1719.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1719.rational a+Real.sqrt 2*evalQPoly rf1719.irrational a)/evalQPoly rf1719.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1719,rf1673]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := 0
theorem eval5 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf0013,rf1673]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := 0
theorem eval6 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf0013,rf1673]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/8 : ℚ)*Polynomial.X^0 + Polynomial.C (5/2 : ℚ)*Polynomial.X^1 + Polynomial.C (-141/8 : ℚ)*Polynomial.X^2 + Polynomial.C (58 : ℚ)*Polynomial.X^3 + Polynomial.C (-851/8 : ℚ)*Polynomial.X^4 + Polynomial.C (207/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-351/8 : ℚ)*Polynomial.X^6
theorem eval7 (a : ℝ) (h : rf1788.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1788.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1788.rational a+Real.sqrt 2*evalQPoly rf1788.irrational a)/evalQPoly rf1788.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1788,rf1673]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := 0
theorem eval8 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf0013,rf1673]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := 0
theorem eval9 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf0013,rf1673]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (7/4 : ℚ)*Polynomial.X^0 + Polynomial.C (-47/4 : ℚ)*Polynomial.X^1 + Polynomial.C (79/2 : ℚ)*Polynomial.X^2 + Polynomial.C (-139/2 : ℚ)*Polynomial.X^3 + Polynomial.C (259/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-99/4 : ℚ)*Polynomial.X^5
theorem eval10 (a : ℝ) (h : rf1879.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1879.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1879.rational a+Real.sqrt 2*evalQPoly rf1879.irrational a)/evalQPoly rf1879.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1879,rf1673]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := 0
theorem eval11 (a : ℝ) (h : rf0013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf0013.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf0013.rational a+Real.sqrt 2*evalQPoly rf0013.irrational a)/evalQPoly rf0013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf0013,rf1673]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even082
