import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd042
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1926.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-53/140 : ℚ)*Polynomial.X^2 + Polynomial.C (163/140 : ℚ)*Polynomial.X^3 + Polynomial.C (71/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-217/20 : ℚ)*Polynomial.X^5 + Polynomial.C (3893/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-5203/140 : ℚ)*Polynomial.X^7 + Polynomial.C (3793/140 : ℚ)*Polynomial.X^8 + Polynomial.C (3/10 : ℚ)*Polynomial.X^9 + Polynomial.C (-66/7 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1926.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1926.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1926.rational a+Real.sqrt 2*evalQPoly rf1926.irrational a)/evalQPoly rf1926.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1926,rf1926]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^1 + Polynomial.C (3/14 : ℚ)*Polynomial.X^2 + Polynomial.C (79/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-197/35 : ℚ)*Polynomial.X^4 + Polynomial.C (404/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-199/14 : ℚ)*Polynomial.X^6 + Polynomial.C (125/14 : ℚ)*Polynomial.X^7 + Polynomial.C (101/70 : ℚ)*Polynomial.X^8 + Polynomial.C (-59/14 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1945.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1945.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1945.rational a+Real.sqrt 2*evalQPoly rf1945.irrational a)/evalQPoly rf1945.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1945,rf1926]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/140 : ℚ)*Polynomial.X^1 + Polynomial.C (37/140 : ℚ)*Polynomial.X^2 + Polynomial.C (97/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/20 : ℚ)*Polynomial.X^5 + Polynomial.C (411/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-47/20 : ℚ)*Polynomial.X^7 + Polynomial.C (7/4 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1982.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1982.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1982.rational a+Real.sqrt 2*evalQPoly rf1982.irrational a)/evalQPoly rf1982.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1982,rf1926]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-61/140 : ℚ)*Polynomial.X^2 + Polynomial.C (241/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-403/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-813/140 : ℚ)*Polynomial.X^5 + Polynomial.C (135/4 : ℚ)*Polynomial.X^6 + Polynomial.C (-8849/140 : ℚ)*Polynomial.X^7 + Polynomial.C (2459/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-507/14 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1963.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1963.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1963.rational a+Real.sqrt 2*evalQPoly rf1963.irrational a)/evalQPoly rf1963.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1963,rf1926]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (2/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-143/35 : ℚ)*Polynomial.X^4 + Polynomial.C (458/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-802/35 : ℚ)*Polynomial.X^6 + Polynomial.C (901/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-97/7 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2000.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2000.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2000.rational a+Real.sqrt 2*evalQPoly rf2000.irrational a)/evalQPoly rf2000.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2000,rf1926]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/140 : ℚ)*Polynomial.X^1 + Polynomial.C (83/140 : ℚ)*Polynomial.X^2 + Polynomial.C (7/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-347/140 : ℚ)*Polynomial.X^4 + Polynomial.C (111/140 : ℚ)*Polynomial.X^5 + Polynomial.C (17/28 : ℚ)*Polynomial.X^6 + Polynomial.C (5/4 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2037.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2037.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2037.rational a+Real.sqrt 2*evalQPoly rf2037.irrational a)/evalQPoly rf2037.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2037,rf1926]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (11/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-73/28 : ℚ)*Polynomial.X^4 + Polynomial.C (303/20 : ℚ)*Polynomial.X^5 + Polynomial.C (-537/20 : ℚ)*Polynomial.X^6 + Polynomial.C (3933/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-437/28 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2018.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2018.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2018.rational a+Real.sqrt 2*evalQPoly rf2018.irrational a)/evalQPoly rf2018.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2018,rf1926]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (1/5 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-143/70 : ℚ)*Polynomial.X^3 + Polynomial.C (229/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-401/35 : ℚ)*Polynomial.X^5 + Polynomial.C (901/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-97/14 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2055.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2055.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2055.rational a+Real.sqrt 2*evalQPoly rf2055.irrational a)/evalQPoly rf2055.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2055,rf1926]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (19/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-111/140 : ℚ)*Polynomial.X^3 + Polynomial.C (57/140 : ℚ)*Polynomial.X^4 + Polynomial.C (29/20 : ℚ)*Polynomial.X^5 + Polynomial.C (-95/28 : ℚ)*Polynomial.X^6 + Polynomial.C (5/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2073.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2073.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2073.rational a+Real.sqrt 2*evalQPoly rf2073.irrational a)/evalQPoly rf2073.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2073,rf1926]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd042
