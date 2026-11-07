import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd053
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1937.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/280 : ℚ)*Polynomial.X^1 + Polynomial.C (3/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^3 + Polynomial.C (193/140 : ℚ)*Polynomial.X^4 + Polynomial.C (61/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-981/140 : ℚ)*Polynomial.X^6 + Polynomial.C (159/20 : ℚ)*Polynomial.X^7 + Polynomial.C (97/20 : ℚ)*Polynomial.X^8 + Polynomial.C (-3089/280 : ℚ)*Polynomial.X^9 + Polynomial.C (-162/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1937.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1937.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1937.rational a+Real.sqrt 2*evalQPoly rf1937.irrational a)/evalQPoly rf1937.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1937,rf1937]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (13/280 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/140 : ℚ)*Polynomial.X^2 + Polynomial.C (37/140 : ℚ)*Polynomial.X^3 + Polynomial.C (24/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-76/35 : ℚ)*Polynomial.X^5 + Polynomial.C (29/140 : ℚ)*Polynomial.X^6 + Polynomial.C (77/20 : ℚ)*Polynomial.X^7 + Polynomial.C (-83/56 : ℚ)*Polynomial.X^8 + Polynomial.C (-333/280 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1956.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1956.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1956.rational a+Real.sqrt 2*evalQPoly rf1956.irrational a)/evalQPoly rf1956.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1956,rf1937]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (59/140 : ℚ)*Polynomial.X^3 + Polynomial.C (43/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-383/140 : ℚ)*Polynomial.X^5 + Polynomial.C (23/28 : ℚ)*Polynomial.X^6 + Polynomial.C (59/20 : ℚ)*Polynomial.X^7 + Polynomial.C (7/8 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1993.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1993.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1993.rational a+Real.sqrt 2*evalQPoly rf1993.irrational a)/evalQPoly rf1993.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1993,rf1937]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/280 : ℚ)*Polynomial.X^1 + Polynomial.C (31/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/35 : ℚ)*Polynomial.X^3 + Polynomial.C (37/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-167/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-17/4 : ℚ)*Polynomial.X^6 + Polynomial.C (514/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-397/56 : ℚ)*Polynomial.X^8 + Polynomial.C (-5149/280 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1974.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1974.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1974.rational a+Real.sqrt 2*evalQPoly rf1974.irrational a)/evalQPoly rf1974.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1974,rf1937]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/140 : ℚ)*Polynomial.X^2 + Polynomial.C (39/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-17/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-45/28 : ℚ)*Polynomial.X^5 + Polynomial.C (339/140 : ℚ)*Polynomial.X^6 + Polynomial.C (101/28 : ℚ)*Polynomial.X^7 + Polynomial.C (-631/140 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2011.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2011.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2011.rational a+Real.sqrt 2*evalQPoly rf2011.irrational a)/evalQPoly rf2011.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2011,rf1937]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/28 : ℚ)*Polynomial.X^2 + Polynomial.C (22/35 : ℚ)*Polynomial.X^3 + Polynomial.C (141/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-253/70 : ℚ)*Polynomial.X^5 + Polynomial.C (421/140 : ℚ)*Polynomial.X^6 + Polynomial.C (3 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2048.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2048.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2048.rational a+Real.sqrt 2*evalQPoly rf2048.irrational a)/evalQPoly rf2048.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2048,rf1937]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^2 + Polynomial.C (7/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-13/35 : ℚ)*Polynomial.X^5 + Polynomial.C (621/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-65/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-2487/280 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2029.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2029.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2029.rational a+Real.sqrt 2*evalQPoly rf2029.irrational a)/evalQPoly rf2029.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2029,rf1937]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (41/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^4 + Polynomial.C (331/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-17/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-193/140 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2066.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2066.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2066.rational a+Real.sqrt 2*evalQPoly rf2066.irrational a)/evalQPoly rf2066.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2066,rf1937]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-71/140 : ℚ)*Polynomial.X^3 + Polynomial.C (1/5 : ℚ)*Polynomial.X^4 + Polynomial.C (293/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-43/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2082.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2082.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2082.rational a+Real.sqrt 2*evalQPoly rf2082.irrational a)/evalQPoly rf2082.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2082,rf1937]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd053
