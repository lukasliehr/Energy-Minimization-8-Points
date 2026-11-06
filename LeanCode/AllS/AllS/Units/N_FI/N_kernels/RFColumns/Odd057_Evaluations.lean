import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd057
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1941.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/280 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/28 : ℚ)*Polynomial.X^2 + Polynomial.C (309/280 : ℚ)*Polynomial.X^3 + Polynomial.C (-99/35 : ℚ)*Polynomial.X^4 + Polynomial.C (173/140 : ℚ)*Polynomial.X^5 + Polynomial.C (57/10 : ℚ)*Polynomial.X^6 + Polynomial.C (-701/140 : ℚ)*Polynomial.X^7 + Polynomial.C (167/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-7101/280 : ℚ)*Polynomial.X^9 + Polynomial.C (2859/140 : ℚ)*Polynomial.X^10 + Polynomial.C (-1051/280 : ℚ)*Polynomial.X^11 + Polynomial.C (-248/35 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1941.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1941.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1941.rational a+Real.sqrt 2*evalQPoly rf1941.irrational a)/evalQPoly rf1941.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1941,rf1941]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/280 : ℚ)*Polynomial.X^1 + Polynomial.C (11/56 : ℚ)*Polynomial.X^2 + Polynomial.C (-71/280 : ℚ)*Polynomial.X^3 + Polynomial.C (13/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-211/140 : ℚ)*Polynomial.X^5 + Polynomial.C (447/140 : ℚ)*Polynomial.X^6 + Polynomial.C (459/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-3371/280 : ℚ)*Polynomial.X^8 + Polynomial.C (487/56 : ℚ)*Polynomial.X^9 + Polynomial.C (31/56 : ℚ)*Polynomial.X^10 + Polynomial.C (-607/280 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1960.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1960.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1960.rational a+Real.sqrt 2*evalQPoly rf1960.irrational a)/evalQPoly rf1960.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1960,rf1941]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (3/56 : ℚ)*Polynomial.X^2 + Polynomial.C (13/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-101/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-137/70 : ℚ)*Polynomial.X^5 + Polynomial.C (437/140 : ℚ)*Polynomial.X^6 + Polynomial.C (131/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-1207/280 : ℚ)*Polynomial.X^8 + Polynomial.C (247/140 : ℚ)*Polynomial.X^9 + Polynomial.C (13/8 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1997.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1997.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1997.rational a+Real.sqrt 2*evalQPoly rf1997.irrational a)/evalQPoly rf1997.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1997,rf1941]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (3/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-183/280 : ℚ)*Polynomial.X^2 + Polynomial.C (809/280 : ℚ)*Polynomial.X^3 + Polynomial.C (-831/140 : ℚ)*Polynomial.X^4 + Polynomial.C (13/20 : ℚ)*Polynomial.X^5 + Polynomial.C (523/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-661/28 : ℚ)*Polynomial.X^7 + Polynomial.C (607/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-7499/280 : ℚ)*Polynomial.X^9 + Polynomial.C (11817/280 : ℚ)*Polynomial.X^10 + Polynomial.C (-7831/280 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1978.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1978.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1978.rational a+Real.sqrt 2*evalQPoly rf1978.irrational a)/evalQPoly rf1978.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1978,rf1941]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/140 : ℚ)*Polynomial.X^1 + Polynomial.C (1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-33/35 : ℚ)*Polynomial.X^3 + Polynomial.C (9/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-19/14 : ℚ)*Polynomial.X^5 + Polynomial.C (187/70 : ℚ)*Polynomial.X^6 + Polynomial.C (209/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-141/7 : ℚ)*Polynomial.X^8 + Polynomial.C (2689/140 : ℚ)*Polynomial.X^9 + Polynomial.C (-969/140 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf2015.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2015.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2015.rational a+Real.sqrt 2*evalQPoly rf2015.irrational a)/evalQPoly rf2015.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2015,rf1941]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^3 + Polynomial.C (5/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-27/35 : ℚ)*Polynomial.X^5 + Polynomial.C (162/35 : ℚ)*Polynomial.X^6 + Polynomial.C (68/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-1089/140 : ℚ)*Polynomial.X^8 + Polynomial.C (11/2 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf2052.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2052.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2052.rational a+Real.sqrt 2*evalQPoly rf2052.irrational a)/evalQPoly rf2052.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2052,rf1941]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/280 : ℚ)*Polynomial.X^2 + Polynomial.C (4/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-243/140 : ℚ)*Polynomial.X^4 + Polynomial.C (27/35 : ℚ)*Polynomial.X^5 + Polynomial.C (349/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-744/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-537/280 : ℚ)*Polynomial.X^8 + Polynomial.C (275/14 : ℚ)*Polynomial.X^9 + Polynomial.C (-3373/280 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf2033.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2033.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2033.rational a+Real.sqrt 2*evalQPoly rf2033.irrational a)/evalQPoly rf2033.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2033,rf1941]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/70 : ℚ)*Polynomial.X^3 + Polynomial.C (2 : ℚ)*Polynomial.X^4 + Polynomial.C (11/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-319/70 : ℚ)*Polynomial.X^6 + Polynomial.C (97/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-799/140 : ℚ)*Polynomial.X^8 + Polynomial.C (233/140 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf2070.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2070.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2070.rational a+Real.sqrt 2*evalQPoly rf2070.irrational a)/evalQPoly rf2070.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2070,rf1941]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/140 : ℚ)*Polynomial.X^1 + Polynomial.C (89/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/14 : ℚ)*Polynomial.X^3 + Polynomial.C (9/70 : ℚ)*Polynomial.X^4 + Polynomial.C (66/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-849/70 : ℚ)*Polynomial.X^6 + Polynomial.C (757/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-209/35 : ℚ)*Polynomial.X^8 + Polynomial.C (13/4 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf2086.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2086.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2086.rational a+Real.sqrt 2*evalQPoly rf2086.irrational a)/evalQPoly rf2086.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2086,rf1941]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd057
