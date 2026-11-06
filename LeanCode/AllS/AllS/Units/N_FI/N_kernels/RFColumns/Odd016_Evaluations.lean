import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd016
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1223.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (19/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^3 + Polynomial.C (88/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-1332/35 : ℚ)*Polynomial.X^5 + Polynomial.C (2139/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-1039/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-1572/35 : ℚ)*Polynomial.X^8 + Polynomial.C (423/10 : ℚ)*Polynomial.X^9 + Polynomial.C (291/14 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1223.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1223.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1223.rational a+Real.sqrt 2*evalQPoly rf1223.irrational a)/evalQPoly rf1223.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1223,rf1223]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (1/4 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/7 : ℚ)*Polynomial.X^2 + Polynomial.C (15/2 : ℚ)*Polynomial.X^3 + Polynomial.C (-87/5 : ℚ)*Polynomial.X^4 + Polynomial.C (151/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-289/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-117/14 : ℚ)*Polynomial.X^7 + Polynomial.C (327/70 : ℚ)*Polynomial.X^8 + Polynomial.C (53/28 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1234.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1234.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1234.rational a+Real.sqrt 2*evalQPoly rf1234.irrational a)/evalQPoly rf1234.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1234,rf1223]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-48/35 : ℚ)*Polynomial.X^2 + Polynomial.C (124/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-56/5 : ℚ)*Polynomial.X^5 + Polynomial.C (24 : ℚ)*Polynomial.X^6 + Polynomial.C (-396/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-19/2 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1254.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1254.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1254.rational a+Real.sqrt 2*evalQPoly rf1254.irrational a)/evalQPoly rf1254.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1254,rf1223]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (51/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/35 : ℚ)*Polynomial.X^2 + Polynomial.C (237/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-447/10 : ℚ)*Polynomial.X^5 + Polynomial.C (4759/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-5829/35 : ℚ)*Polynomial.X^7 + Polynomial.C (6529/140 : ℚ)*Polynomial.X^8 + Polynomial.C (1747/28 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1243.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1243.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1243.rational a+Real.sqrt 2*evalQPoly rf1243.irrational a)/evalQPoly rf1243.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1243,rf1223]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/35 : ℚ)*Polynomial.X^2 + Polynomial.C (202/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-699/35 : ℚ)*Polynomial.X^4 + Polynomial.C (262/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-1109/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^7 + Polynomial.C (67/7 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf1263.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1263.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1263.rational a+Real.sqrt 2*evalQPoly rf1263.irrational a)/evalQPoly rf1263.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1263,rf1223]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^1 + Polynomial.C (79/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/14 : ℚ)*Polynomial.X^3 + Polynomial.C (-121/70 : ℚ)*Polynomial.X^4 + Polynomial.C (743/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-599/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-13/2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf1282.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1282.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1282.rational a+Real.sqrt 2*evalQPoly rf1282.irrational a)/evalQPoly rf1282.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1282,rf1223]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (6/35 : ℚ)*Polynomial.X^2 + Polynomial.C (113/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-129/7 : ℚ)*Polynomial.X^4 + Polynomial.C (1573/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-1802/35 : ℚ)*Polynomial.X^6 + Polynomial.C (383/35 : ℚ)*Polynomial.X^7 + Polynomial.C (253/14 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1273.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1273.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1273.rational a+Real.sqrt 2*evalQPoly rf1273.irrational a)/evalQPoly rf1273.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1273,rf1223]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/70 : ℚ)*Polynomial.X^1 + Polynomial.C (20/7 : ℚ)*Polynomial.X^2 + Polynomial.C (-681/70 : ℚ)*Polynomial.X^3 + Polynomial.C (91/5 : ℚ)*Polynomial.X^4 + Polynomial.C (-1153/70 : ℚ)*Polynomial.X^5 + Polynomial.C (62/35 : ℚ)*Polynomial.X^6 + Polynomial.C (53/14 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf1292.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1292.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1292.rational a+Real.sqrt 2*evalQPoly rf1292.irrational a)/evalQPoly rf1292.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1292,rf1223]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/35 : ℚ)*Polynomial.X^1 + Polynomial.C (57/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-15/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-25/7 : ℚ)*Polynomial.X^4 + Polynomial.C (89/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-43/5 : ℚ)*Polynomial.X^6 + Polynomial.C (-7 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf1302.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1302.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1302.rational a+Real.sqrt 2*evalQPoly rf1302.irrational a)/evalQPoly rf1302.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1302,rf1223]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd016
