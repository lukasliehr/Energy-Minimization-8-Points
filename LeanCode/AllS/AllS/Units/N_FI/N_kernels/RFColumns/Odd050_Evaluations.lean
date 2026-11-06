import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd050
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1934.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (53/28 : ℚ)*Polynomial.X^3 + Polynomial.C (-279/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-48/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1431/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-4061/140 : ℚ)*Polynomial.X^7 + Polynomial.C (417/70 : ℚ)*Polynomial.X^8 + Polynomial.C (311/40 : ℚ)*Polynomial.X^9 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1934.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1934.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1934.rational a+Real.sqrt 2*evalQPoly rf1934.irrational a)/evalQPoly rf1934.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1934,rf1934]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (3/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-39/280 : ℚ)*Polynomial.X^1 + Polynomial.C (22/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-32/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-197/140 : ℚ)*Polynomial.X^4 + Polynomial.C (173/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-36/5 : ℚ)*Polynomial.X^6 + Polynomial.C (24/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-41/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-379/280 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1953.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1953.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1953.rational a+Real.sqrt 2*evalQPoly rf1953.irrational a)/evalQPoly rf1953.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1953,rf1934]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (3/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (87/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-22/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-21/10 : ℚ)*Polynomial.X^4 + Polynomial.C (156/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-11/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-5/8 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1990.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1990.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1990.rational a+Real.sqrt 2*evalQPoly rf1990.irrational a)/evalQPoly rf1990.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1990,rf1934]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (13/280 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^2 + Polynomial.C (111/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-137/28 : ℚ)*Polynomial.X^4 + Polynomial.C (667/140 : ℚ)*Polynomial.X^5 + Polynomial.C (77/5 : ℚ)*Polynomial.X^6 + Polynomial.C (-3247/70 : ℚ)*Polynomial.X^7 + Polynomial.C (9659/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-547/280 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1971.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1971.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1971.rational a+Real.sqrt 2*evalQPoly rf1971.irrational a)/evalQPoly rf1971.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1971,rf1934]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (33/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-113/70 : ℚ)*Polynomial.X^3 + Polynomial.C (9/10 : ℚ)*Polynomial.X^4 + Polynomial.C (407/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-853/70 : ℚ)*Polynomial.X^6 + Polynomial.C (717/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-379/70 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2008.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2008.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2008.rational a+Real.sqrt 2*evalQPoly rf2008.irrational a)/evalQPoly rf2008.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2008,rf1934]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/70 : ℚ)*Polynomial.X^1 + Polynomial.C (29/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-19/10 : ℚ)*Polynomial.X^4 + Polynomial.C (93/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-111/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2045.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2045.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2045.rational a+Real.sqrt 2*evalQPoly rf2045.irrational a)/evalQPoly rf2045.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2045,rf1934]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/280 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (5/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-153/70 : ℚ)*Polynomial.X^3 + Polynomial.C (281/70 : ℚ)*Polynomial.X^4 + Polynomial.C (309/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-2789/140 : ℚ)*Polynomial.X^6 + Polynomial.C (1223/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-361/280 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2026.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2026.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2026.rational a+Real.sqrt 2*evalQPoly rf2026.irrational a)/evalQPoly rf2026.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2026,rf1934]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (33/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-111/140 : ℚ)*Polynomial.X^2 + Polynomial.C (9/28 : ℚ)*Polynomial.X^3 + Polynomial.C (443/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-809/140 : ℚ)*Polynomial.X^5 + Polynomial.C (583/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-309/140 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2063.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2063.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2063.rational a+Real.sqrt 2*evalQPoly rf2063.irrational a)/evalQPoly rf2063.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2063,rf1934]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (9/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-59/140 : ℚ)*Polynomial.X^3 + Polynomial.C (97/140 : ℚ)*Polynomial.X^4 + Polynomial.C (127/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-67/140 : ℚ)*Polynomial.X^6 + Polynomial.C (1/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2080.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2080.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2080.rational a+Real.sqrt 2*evalQPoly rf2080.irrational a)/evalQPoly rf2080.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2080,rf1934]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd050
