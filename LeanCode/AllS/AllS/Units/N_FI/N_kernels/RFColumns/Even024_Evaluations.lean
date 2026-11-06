import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even024
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1055.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-361/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (579/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-71/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-35877/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (44663/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-362522/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (82701/1610 : ℚ)*Polynomial.X^8 + Polynomial.C (-1344841/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-167593/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (1156759/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-2524231/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-93773/3910 : ℚ)*Polynomial.X^13
theorem eval0 (a : ℝ) (h : rf1055.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1055.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1055.rational a+Real.sqrt 2*evalQPoly rf1055.irrational a)/evalQPoly rf1055.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1055,rf1055]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-39/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (479/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (61/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-7453/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (8206/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-102513/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (81421/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (33112/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-739811/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1498747/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (10247/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (-2793/85 : ℚ)*Polynomial.X^12
theorem eval1 (a : ℝ) (h : rf1070.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1070.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1070.rational a+Real.sqrt 2*evalQPoly rf1070.irrational a)/evalQPoly rf1070.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1070,rf1055]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-87/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (6/595 : ℚ)*Polynomial.X^2 + Polynomial.C (53/2380 : ℚ)*Polynomial.X^3 + Polynomial.C (-8528/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (4303/1190 : ℚ)*Polynomial.X^5 + Polynomial.C (-30062/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (540287/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-36807/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (8657/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (25796/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-363/92 : ℚ)*Polynomial.X^11
theorem eval2 (a : ℝ) (h : rf1098.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1098.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1098.rational a+Real.sqrt 2*evalQPoly rf1098.irrational a)/evalQPoly rf1098.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1098,rf1055]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^2 + Polynomial.C (-12/805 : ℚ)*Polynomial.X^3 + Polynomial.C (-18/805 : ℚ)*Polynomial.X^4 + Polynomial.C (1726/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-330/161 : ℚ)*Polynomial.X^6 + Polynomial.C (27588/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (45139/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-180539/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (1521/115 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1140.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1140.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1140.rational a+Real.sqrt 2*evalQPoly rf1140.irrational a)/evalQPoly rf1140.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1140,rf1055]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (-361/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (39/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (1297/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (-21433/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (45307/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-367548/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (111844/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-1969963/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (1171579/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (1283/17 : ℚ)*Polynomial.X^11 + Polynomial.C (-670469/7820 : ℚ)*Polynomial.X^12
theorem eval4 (a : ℝ) (h : rf1083.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1083.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1083.rational a+Real.sqrt 2*evalQPoly rf1083.irrational a)/evalQPoly rf1083.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1083,rf1055]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (292/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-159/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-8664/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (8927/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-196114/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (274691/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (136567/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-350471/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (287042/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-361277/3910 : ℚ)*Polynomial.X^11
theorem eval5 (a : ℝ) (h : rf1112.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1112.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1112.rational a+Real.sqrt 2*evalQPoly rf1112.irrational a)/evalQPoly rf1112.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1112,rf1055]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-27/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (131/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (802/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-15557/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (35907/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-238649/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (17706/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-1885337/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (5739/230 : ℚ)*Polynomial.X^9 + Polynomial.C (-1751/460 : ℚ)*Polynomial.X^10
theorem eval6 (a : ℝ) (h : rf1153.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1153.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1153.rational a+Real.sqrt 2*evalQPoly rf1153.irrational a)/evalQPoly rf1153.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1153,rf1055]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (709/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-1443/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (957/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (11882/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-191339/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (17926/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-2468581/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (772027/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-315881/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (39611/1955 : ℚ)*Polynomial.X^11
theorem eval7 (a : ℝ) (h : rf1125.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1125.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1125.rational a+Real.sqrt 2*evalQPoly rf1125.irrational a)/evalQPoly rf1125.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1125,rf1055]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-3/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (107/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-457/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-1016/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (11986/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-40729/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (52083/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (48644/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-38829/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (18949/782 : ℚ)*Polynomial.X^9 + Polynomial.C (-22099/3910 : ℚ)*Polynomial.X^10
theorem eval8 (a : ℝ) (h : rf1167.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1167.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1167.rational a+Real.sqrt 2*evalQPoly rf1167.irrational a)/evalQPoly rf1167.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1167,rf1055]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (67/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-8/391 : ℚ)*Polynomial.X^2 + Polynomial.C (20/391 : ℚ)*Polynomial.X^3 + Polynomial.C (5417/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-50357/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (34380/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-294736/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (75151/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (-363/46 : ℚ)*Polynomial.X^9
theorem eval9 (a : ℝ) (h : rf1195.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1195.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1195.rational a+Real.sqrt 2*evalQPoly rf1195.irrational a)/evalQPoly rf1195.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1195,rf1055]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (87/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (-886/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (169/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (2549/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-26391/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (76066/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (46859/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-115261/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (268723/7820 : ℚ)*Polynomial.X^10
theorem eval10 (a : ℝ) (h : rf1180.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1180.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1180.rational a+Real.sqrt 2*evalQPoly rf1180.irrational a)/evalQPoly rf1180.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1180,rf1055]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (7/1955 : ℚ)*Polynomial.X^1 + Polynomial.C (-258/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-978/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (13114/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1256/391 : ℚ)*Polynomial.X^5 + Polynomial.C (49594/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (3874/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-8400/391 : ℚ)*Polynomial.X^8 + Polynomial.C (45297/1955 : ℚ)*Polynomial.X^9
theorem eval11 (a : ℝ) (h : rf1209.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1209.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1209.rational a+Real.sqrt 2*evalQPoly rf1209.irrational a)/evalQPoly rf1209.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1209,rf1055]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even024
