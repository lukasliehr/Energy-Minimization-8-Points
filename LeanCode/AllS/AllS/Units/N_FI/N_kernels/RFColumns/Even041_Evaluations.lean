import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even041
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1312.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-31/238 : ℚ)*Polynomial.X^1 + Polynomial.C (57/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-2357/238 : ℚ)*Polynomial.X^3 + Polynomial.C (144/17 : ℚ)*Polynomial.X^4 + Polynomial.C (9084/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-71307/238 : ℚ)*Polynomial.X^6 + Polynomial.C (53826/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-14718/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-128897/238 : ℚ)*Polynomial.X^9 + Polynomial.C (265989/476 : ℚ)*Polynomial.X^10 + Polynomial.C (5471/34 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1312.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1312.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1312.rational a+Real.sqrt 2*evalQPoly rf1312.irrational a)/evalQPoly rf1312.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1312,rf1312]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-6/119 : ℚ)*Polynomial.X^0 + Polynomial.C (349/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-386/119 : ℚ)*Polynomial.X^2 + Polynomial.C (569/238 : ℚ)*Polynomial.X^3 + Polynomial.C (4863/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-6653/119 : ℚ)*Polynomial.X^5 + Polynomial.C (117/34 : ℚ)*Polynomial.X^6 + Polynomial.C (39359/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-6849/34 : ℚ)*Polynomial.X^8 + Polynomial.C (-40281/476 : ℚ)*Polynomial.X^9 + Polynomial.C (11635/34 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1331.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1331.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1331.rational a+Real.sqrt 2*evalQPoly rf1331.irrational a)/evalQPoly rf1331.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1331,rf1312]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/68 : ℚ)*Polynomial.X^1 + Polynomial.C (401/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-3567/238 : ℚ)*Polynomial.X^3 + Polynomial.C (14785/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-12639/119 : ℚ)*Polynomial.X^5 + Polynomial.C (8027/238 : ℚ)*Polynomial.X^6 + Polynomial.C (34143/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-51053/238 : ℚ)*Polynomial.X^8 + Polynomial.C (121/4 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1367.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1367.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1367.rational a+Real.sqrt 2*evalQPoly rf1367.irrational a)/evalQPoly rf1367.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1367,rf1312]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (1/17 : ℚ)*Polynomial.X^0 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^1 + Polynomial.C (538/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-258/17 : ℚ)*Polynomial.X^3 + Polynomial.C (4184/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-1650/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-13082/119 : ℚ)*Polynomial.X^6 + Polynomial.C (4074/17 : ℚ)*Polynomial.X^7 + Polynomial.C (-217 : ℚ)*Polynomial.X^8
theorem eval3 (a : ℝ) (h : rf1421.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1421.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1421.rational a+Real.sqrt 2*evalQPoly rf1421.irrational a)/evalQPoly rf1421.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1421,rf1312]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/7 : ℚ)*Polynomial.X^1 + Polynomial.C (2269/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-341/17 : ℚ)*Polynomial.X^3 + Polynomial.C (4443/119 : ℚ)*Polynomial.X^4 + Polynomial.C (3517/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-73119/238 : ℚ)*Polynomial.X^6 + Polynomial.C (84719/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-166881/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-3253/119 : ℚ)*Polynomial.X^9 + Polynomial.C (44879/68 : ℚ)*Polynomial.X^10
theorem eval4 (a : ℝ) (h : rf1348.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1348.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1348.rational a+Real.sqrt 2*evalQPoly rf1348.irrational a)/evalQPoly rf1348.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1348,rf1312]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (3/476 : ℚ)*Polynomial.X^0 + Polynomial.C (59/476 : ℚ)*Polynomial.X^1 + Polynomial.C (-55/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-2627/238 : ℚ)*Polynomial.X^3 + Polynomial.C (8490/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-19920/119 : ℚ)*Polynomial.X^5 + Polynomial.C (18503/238 : ℚ)*Polynomial.X^6 + Polynomial.C (107683/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-68253/68 : ℚ)*Polynomial.X^8 + Polynomial.C (57043/68 : ℚ)*Polynomial.X^9
theorem eval5 (a : ℝ) (h : rf1385.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1385.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1385.rational a+Real.sqrt 2*evalQPoly rf1385.irrational a)/evalQPoly rf1385.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1385,rf1312]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/68 : ℚ)*Polynomial.X^0 + Polynomial.C (87/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-332/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-53/7 : ℚ)*Polynomial.X^3 + Polynomial.C (13967/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-2029/17 : ℚ)*Polynomial.X^5 + Polynomial.C (12890/119 : ℚ)*Polynomial.X^6 + Polynomial.C (57/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-391/4 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf1438.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1438.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1438.rational a+Real.sqrt 2*evalQPoly rf1438.irrational a)/evalQPoly rf1438.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1438,rf1312]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-208/119 : ℚ)*Polynomial.X^2 + Polynomial.C (1389/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-1765/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-9257/119 : ℚ)*Polynomial.X^5 + Polynomial.C (28990/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-44057/119 : ℚ)*Polynomial.X^7 + Polynomial.C (81547/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-796/17 : ℚ)*Polynomial.X^9
theorem eval7 (a : ℝ) (h : rf1402.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1402.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1402.rational a+Real.sqrt 2*evalQPoly rf1402.irrational a)/evalQPoly rf1402.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1402,rf1312]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (3/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-111/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-141/238 : ℚ)*Polynomial.X^2 + Polynomial.C (3645/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-4656/119 : ℚ)*Polynomial.X^4 + Polynomial.C (21/2 : ℚ)*Polynomial.X^5 + Polynomial.C (22989/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-7335/34 : ℚ)*Polynomial.X^7 + Polynomial.C (5565/68 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1456.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1456.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1456.rational a+Real.sqrt 2*evalQPoly rf1456.irrational a)/evalQPoly rf1456.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1456,rf1312]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (159/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-1055/238 : ℚ)*Polynomial.X^2 + Polynomial.C (2383/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-5693/238 : ℚ)*Polynomial.X^4 + Polynomial.C (15829/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-21277/238 : ℚ)*Polynomial.X^6 + Polynomial.C (107/2 : ℚ)*Polynomial.X^7
theorem eval9 (a : ℝ) (h : rf1492.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1492.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1492.rational a+Real.sqrt 2*evalQPoly rf1492.irrational a)/evalQPoly rf1492.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1492,rf1312]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (5/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-396/119 : ℚ)*Polynomial.X^2 + Polynomial.C (1675/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-2019/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-6751/119 : ℚ)*Polynomial.X^5 + Polynomial.C (10974/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-3887/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-12653/68 : ℚ)*Polynomial.X^8
theorem eval10 (a : ℝ) (h : rf1473.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1473.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1473.rational a+Real.sqrt 2*evalQPoly rf1473.irrational a)/evalQPoly rf1473.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1473,rf1312]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-3/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-23/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-359/238 : ℚ)*Polynomial.X^2 + Polynomial.C (4133/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-8601/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-3701/238 : ℚ)*Polynomial.X^5 + Polynomial.C (3685/34 : ℚ)*Polynomial.X^6 + Polynomial.C (-6559/34 : ℚ)*Polynomial.X^7
theorem eval11 (a : ℝ) (h : rf1510.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1510.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1510.rational a+Real.sqrt 2*evalQPoly rf1510.irrational a)/evalQPoly rf1510.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1510,rf1312]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even041
