import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd037
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1536.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (33/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-10/7 : ℚ)*Polynomial.X^3 + Polynomial.C (17/5 : ℚ)*Polynomial.X^4 + Polynomial.C (11/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-927/70 : ℚ)*Polynomial.X^6 + Polynomial.C (386/35 : ℚ)*Polynomial.X^7 + Polynomial.C (401/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-829/70 : ℚ)*Polynomial.X^9 + Polynomial.C (123/20 : ℚ)*Polynomial.X^10 + Polynomial.C (172/35 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1536.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1536.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1536.rational a+Real.sqrt 2*evalQPoly rf1536.irrational a)/evalQPoly rf1536.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1536,rf1536]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (-67/140 : ℚ)*Polynomial.X^2 + Polynomial.C (51/70 : ℚ)*Polynomial.X^3 + Polynomial.C (57/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-39/14 : ℚ)*Polynomial.X^5 + Polynomial.C (1/70 : ℚ)*Polynomial.X^6 + Polynomial.C (321/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-633/140 : ℚ)*Polynomial.X^8 + Polynomial.C (12/35 : ℚ)*Polynomial.X^9 + Polynomial.C (169/140 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1551.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1551.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1551.rational a+Real.sqrt 2*evalQPoly rf1551.irrational a)/evalQPoly rf1551.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1551,rf1536]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^3 + Polynomial.C (121/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-32/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-74/35 : ℚ)*Polynomial.X^6 + Polynomial.C (4/5 : ℚ)*Polynomial.X^7 + Polynomial.C (-257/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-1 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1579.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1579.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1579.rational a+Real.sqrt 2*evalQPoly rf1579.irrational a)/evalQPoly rf1579.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1579,rf1536]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (37/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/5 : ℚ)*Polynomial.X^3 + Polynomial.C (181/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-14/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-33/2 : ℚ)*Polynomial.X^6 + Polynomial.C (195/7 : ℚ)*Polynomial.X^7 + Polynomial.C (167/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-239/14 : ℚ)*Polynomial.X^9 + Polynomial.C (2577/140 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1565.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1565.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1565.rational a+Real.sqrt 2*evalQPoly rf1565.irrational a)/evalQPoly rf1565.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1565,rf1536]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^2 + Polynomial.C (33/35 : ℚ)*Polynomial.X^3 + Polynomial.C (9/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-127/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-9/35 : ℚ)*Polynomial.X^6 + Polynomial.C (263/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-293/35 : ℚ)*Polynomial.X^8 + Polynomial.C (134/35 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1593.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1593.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1593.rational a+Real.sqrt 2*evalQPoly rf1593.irrational a)/evalQPoly rf1593.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1593,rf1536]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (24/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-118/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^6 + Polynomial.C (104/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-13/4 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1622.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1622.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1622.rational a+Real.sqrt 2*evalQPoly rf1622.irrational a)/evalQPoly rf1622.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1622,rf1536]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (9/70 : ℚ)*Polynomial.X^2 + Polynomial.C (39/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-7/5 : ℚ)*Polynomial.X^4 + Polynomial.C (-61/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-17/70 : ℚ)*Polynomial.X^6 + Polynomial.C (473/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-169/28 : ℚ)*Polynomial.X^8 + Polynomial.C (169/35 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1607.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1607.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1607.rational a+Real.sqrt 2*evalQPoly rf1607.irrational a)/evalQPoly rf1607.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1607,rf1536]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/70 : ℚ)*Polynomial.X^1 + Polynomial.C (11/14 : ℚ)*Polynomial.X^2 + Polynomial.C (-69/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-9/14 : ℚ)*Polynomial.X^4 + Polynomial.C (3/2 : ℚ)*Polynomial.X^5 + Polynomial.C (-207/70 : ℚ)*Polynomial.X^6 + Polynomial.C (249/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-38/35 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1636.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1636.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1636.rational a+Real.sqrt 2*evalQPoly rf1636.irrational a)/evalQPoly rf1636.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1636,rf1536]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (4/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/35 : ℚ)*Polynomial.X^2 + Polynomial.C (44/35 : ℚ)*Polynomial.X^3 + Polynomial.C (17/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-256/35 : ℚ)*Polynomial.X^5 + Polynomial.C (11/7 : ℚ)*Polynomial.X^6 + Polynomial.C (24/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-15/4 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1648.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1648.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1648.rational a+Real.sqrt 2*evalQPoly rf1648.irrational a)/evalQPoly rf1648.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1648,rf1536]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd037
