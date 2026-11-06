import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd017
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1224.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/140 : ℚ)*Polynomial.X^1 + Polynomial.C (1/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-57/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/35 : ℚ)*Polynomial.X^4 + Polynomial.C (319/140 : ℚ)*Polynomial.X^5 + Polynomial.C (88/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-803/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-92/35 : ℚ)*Polynomial.X^8
theorem eval0 (a : ℝ) (h : rf1224.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1224.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1224.rational a+Real.sqrt 2*evalQPoly rf1224.irrational a)/evalQPoly rf1224.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1224,rf1224]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (1/20 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-7/20 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/28 : ℚ)*Polynomial.X^4 + Polynomial.C (233/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-19/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-79/140 : ℚ)*Polynomial.X^7
theorem eval1 (a : ℝ) (h : rf1235.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1235.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1235.rational a+Real.sqrt 2*evalQPoly rf1235.irrational a)/evalQPoly rf1235.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1235,rf1224]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/35 : ℚ)*Polynomial.X^3 + Polynomial.C (37/140 : ℚ)*Polynomial.X^4 + Polynomial.C (27/35 : ℚ)*Polynomial.X^5 + Polynomial.C (1/4 : ℚ)*Polynomial.X^6
theorem eval2 (a : ℝ) (h : rf1255.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1255.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1255.rational a+Real.sqrt 2*evalQPoly rf1255.irrational a)/evalQPoly rf1255.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1255,rf1224]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (7/20 : ℚ)*Polynomial.X^2 + Polynomial.C (-109/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-41/140 : ℚ)*Polynomial.X^4 + Polynomial.C (131/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-47/20 : ℚ)*Polynomial.X^6 + Polynomial.C (-1367/140 : ℚ)*Polynomial.X^7
theorem eval3 (a : ℝ) (h : rf1244.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1244.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1244.rational a+Real.sqrt 2*evalQPoly rf1244.irrational a)/evalQPoly rf1244.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1244,rf1224]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/35 : ℚ)*Polynomial.X^3 + Polynomial.C (17/35 : ℚ)*Polynomial.X^4 + Polynomial.C (193/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-193/70 : ℚ)*Polynomial.X^6
theorem eval4 (a : ℝ) (h : rf1264.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1264.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1264.rational a+Real.sqrt 2*evalQPoly rf1264.irrational a)/evalQPoly rf1264.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1264,rf1224]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^3 + Polynomial.C (111/70 : ℚ)*Polynomial.X^4 + Polynomial.C (1 : ℚ)*Polynomial.X^5
theorem eval5 (a : ℝ) (h : rf1283.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1283.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1283.rational a+Real.sqrt 2*evalQPoly rf1283.irrational a)/evalQPoly rf1283.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1283,rf1224]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/140 : ℚ)*Polynomial.X^2 + Polynomial.C (12/35 : ℚ)*Polynomial.X^3 + Polynomial.C (5/4 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/10 : ℚ)*Polynomial.X^5 + Polynomial.C (-561/140 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1274.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1274.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1274.rational a+Real.sqrt 2*evalQPoly rf1274.irrational a)/evalQPoly rf1274.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1274,rf1224]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (2/5 : ℚ)*Polynomial.X^3 + Polynomial.C (9/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-79/70 : ℚ)*Polynomial.X^5
theorem eval7 (a : ℝ) (h : rf1293.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1293.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1293.rational a+Real.sqrt 2*evalQPoly rf1293.irrational a)/evalQPoly rf1293.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1293,rf1224]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/35 : ℚ)*Polynomial.X^3 + Polynomial.C (19/35 : ℚ)*Polynomial.X^4 + Polynomial.C (1/2 : ℚ)*Polynomial.X^5
theorem eval8 (a : ℝ) (h : rf1303.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1303.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1303.rational a+Real.sqrt 2*evalQPoly rf1303.irrational a)/evalQPoly rf1303.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1303,rf1224]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd017
