import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even029
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1060.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (1/230 : ℚ)*Polynomial.X^4 + Polynomial.C (293/10948 : ℚ)*Polynomial.X^5 + Polynomial.C (-2137/4760 : ℚ)*Polynomial.X^6 + Polynomial.C (143107/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-118868/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (495221/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-528629/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (570851/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-65187/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (16649/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (129573/15640 : ℚ)*Polynomial.X^14 + Polynomial.C (-321641/54740 : ℚ)*Polynomial.X^15 + Polynomial.C (-440/161 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1060.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1060.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1060.rational a+Real.sqrt 2*evalQPoly rf1060.irrational a)/evalQPoly rf1060.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1060,rf1060]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (38/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-4187/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (914/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-9123/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (4621/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-14321/43792 : ℚ)*Polynomial.X^9 + Polynomial.C (-44447/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (180921/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-57881/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (312623/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (6373/5474 : ℚ)*Polynomial.X^14 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1075.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1075.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1075.rational a+Real.sqrt 2*evalQPoly rf1075.irrational a)/evalQPoly rf1075.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1075,rf1060]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-243/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-31/1610 : ℚ)*Polynomial.X^5 + Polynomial.C (635/1564 : ℚ)*Polynomial.X^6 + Polynomial.C (-34837/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (48113/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-245181/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (7674/391 : ℚ)*Polynomial.X^10 + Polynomial.C (-155579/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-485671/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (142937/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (1413/644 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1103.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1103.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1103.rational a+Real.sqrt 2*evalQPoly rf1103.irrational a)/evalQPoly rf1103.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1103,rf1060]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (-33/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-66/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (81/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (281/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-5293/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (66/391 : ℚ)*Polynomial.X^10 + Polynomial.C (19699/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-17601/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (25/92 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1145.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1145.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1145.rational a+Real.sqrt 2*evalQPoly rf1145.irrational a)/evalQPoly rf1145.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1145,rf1060]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (12/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-779/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (7207/15640 : ℚ)*Polynomial.X^5 + Polynomial.C (-10211/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (448199/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-40403/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (1370461/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (46063/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-219432/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (39397/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (159947/21896 : ℚ)*Polynomial.X^13 + Polynomial.C (-91121/27370 : ℚ)*Polynomial.X^14 + Polynomial.C (-3001/644 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1088.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1088.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1088.rational a+Real.sqrt 2*evalQPoly rf1088.irrational a)/evalQPoly rf1088.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1088,rf1060]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-89/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (4979/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-1947/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (75/782 : ℚ)*Polynomial.X^6 + Polynomial.C (202/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-14971/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (-767/1564 : ℚ)*Polynomial.X^9 + Polynomial.C (20051/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (2791/1190 : ℚ)*Polynomial.X^11 + Polynomial.C (-1616663/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (14154/1955 : ℚ)*Polynomial.X^13 + Polynomial.C (-56/23 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1117.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1117.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1117.rational a+Real.sqrt 2*evalQPoly rf1117.irrational a)/evalQPoly rf1117.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1117,rf1060]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (39/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (137/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-21167/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (28682/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-171149/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (148823/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-135837/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (26508/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (203799/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-8983/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (-291/644 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1158.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1158.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1158.rational a+Real.sqrt 2*evalQPoly rf1158.irrational a)/evalQPoly rf1158.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1158,rf1060]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (109/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (523/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-2549/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (64037/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-119067/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (59715/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-1032247/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (555363/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-421319/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-457913/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (35881/5474 : ℚ)*Polynomial.X^13 + Polynomial.C (1877/644 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1130.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1130.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1130.rational a+Real.sqrt 2*evalQPoly rf1130.irrational a)/evalQPoly rf1130.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1130,rf1060]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (39/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (-11/322 : ℚ)*Polynomial.X^5 + Polynomial.C (261/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (601/7820 : ℚ)*Polynomial.X^7 + Polynomial.C (-2598/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-3593/15640 : ℚ)*Polynomial.X^9 + Polynomial.C (23451/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (21139/21896 : ℚ)*Polynomial.X^11 + Polynomial.C (-52827/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (79/92 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1172.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1172.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1172.rational a+Real.sqrt 2*evalQPoly rf1172.irrational a)/evalQPoly rf1172.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1172,rf1060]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^2 + Polynomial.C (-8/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-4/161 : ℚ)*Polynomial.X^4 + Polynomial.C (1147/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-893/391 : ℚ)*Polynomial.X^6 + Polynomial.C (17720/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-26388/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (29695/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (67409/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-44/23 : ℚ)*Polynomial.X^11 + Polynomial.C (-340/161 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1200.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1200.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1200.rational a+Real.sqrt 2*evalQPoly rf1200.irrational a)/evalQPoly rf1200.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1200,rf1060]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/1190 : ℚ)*Polynomial.X^2 + Polynomial.C (9/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (1243/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-21923/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (3809/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-23229/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-35821/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (571709/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-257443/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-58867/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (94959/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (305/92 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1185.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1185.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1185.rational a+Real.sqrt 2*evalQPoly rf1185.irrational a)/evalQPoly rf1185.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1185,rf1060]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/4760 : ℚ)*Polynomial.X^2 + Polynomial.C (87/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-11/340 : ℚ)*Polynomial.X^4 + Polynomial.C (243/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (1/68 : ℚ)*Polynomial.X^6 + Polynomial.C (-3441/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (7673/21896 : ℚ)*Polynomial.X^8 + Polynomial.C (-4269/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-12499/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (1/23 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1214.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1214.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1214.rational a+Real.sqrt 2*evalQPoly rf1214.irrational a)/evalQPoly rf1214.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1214,rf1060]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even029
