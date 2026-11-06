import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd014
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1221.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/70 : ℚ)*Polynomial.X^2 + Polynomial.C (13/28 : ℚ)*Polynomial.X^3 + Polynomial.C (134/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-1731/140 : ℚ)*Polynomial.X^5 + Polynomial.C (617/70 : ℚ)*Polynomial.X^6 + Polynomial.C (93/20 : ℚ)*Polynomial.X^7 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1221.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1221.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1221.rational a+Real.sqrt 2*evalQPoly rf1221.irrational a)/evalQPoly rf1221.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1221,rf1221]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/20 : ℚ)*Polynomial.X^1 + Polynomial.C (1/140 : ℚ)*Polynomial.X^2 + Polynomial.C (237/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-591/140 : ℚ)*Polynomial.X^4 + Polynomial.C (641/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-261/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-137/140 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1232.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1232.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1232.rational a+Real.sqrt 2*evalQPoly rf1232.irrational a)/evalQPoly rf1232.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1232,rf1221]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/70 : ℚ)*Polynomial.X^1 + Polynomial.C (9/28 : ℚ)*Polynomial.X^2 + Polynomial.C (4/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-151/140 : ℚ)*Polynomial.X^4 + Polynomial.C (13/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1252.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1252.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1252.rational a+Real.sqrt 2*evalQPoly rf1252.irrational a)/evalQPoly rf1252.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1252,rf1221]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/140 : ℚ)*Polynomial.X^2 + Polynomial.C (25/28 : ℚ)*Polynomial.X^3 + Polynomial.C (33/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-367/28 : ℚ)*Polynomial.X^5 + Polynomial.C (2827/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-361/140 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1241.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1241.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1241.rational a+Real.sqrt 2*evalQPoly rf1241.irrational a)/evalQPoly rf1241.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1241,rf1221]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (3/7 : ℚ)*Polynomial.X^2 + Polynomial.C (4/5 : ℚ)*Polynomial.X^3 + Polynomial.C (-184/35 : ℚ)*Polynomial.X^4 + Polynomial.C (41/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-207/35 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1261.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1261.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1261.rational a+Real.sqrt 2*evalQPoly rf1261.irrational a)/evalQPoly rf1261.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1261,rf1221]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (9/35 : ℚ)*Polynomial.X^2 + Polynomial.C (39/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-38/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-1 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1280.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1280.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1280.rational a+Real.sqrt 2*evalQPoly rf1280.irrational a)/evalQPoly rf1280.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1280,rf1221]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (15/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-881/140 : ℚ)*Polynomial.X^4 + Polynomial.C (91/10 : ℚ)*Polynomial.X^5 + Polynomial.C (-583/140 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1271.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1271.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1271.rational a+Real.sqrt 2*evalQPoly rf1271.irrational a)/evalQPoly rf1271.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1271,rf1221]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-3/70 : ℚ)*Polynomial.X^0 + Polynomial.C (3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (2/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-92/35 : ℚ)*Polynomial.X^3 + Polynomial.C (41/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-207/70 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1290.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1290.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1290.rational a+Real.sqrt 2*evalQPoly rf1290.irrational a)/evalQPoly rf1290.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1290,rf1221]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-79/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-3/2 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1300.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1300.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1300.rational a+Real.sqrt 2*evalQPoly rf1300.irrational a)/evalQPoly rf1300.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1300,rf1221]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd014
