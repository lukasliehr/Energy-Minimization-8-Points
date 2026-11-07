import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd025
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1524.denominator
def n0 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/56 : ℚ)*Polynomial.X^1 + Polynomial.C (17/40 : ℚ)*Polynomial.X^2 + Polynomial.C (-881/280 : ℚ)*Polynomial.X^3 + Polynomial.C (3039/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-14983/140 : ℚ)*Polynomial.X^5 + Polynomial.C (47237/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-2583/4 : ℚ)*Polynomial.X^7 + Polynomial.C (186097/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-7221/40 : ℚ)*Polynomial.X^9 + Polynomial.C (-81393/280 : ℚ)*Polynomial.X^10 + Polynomial.C (9437/40 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1524.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1524.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1524.rational a+Real.sqrt 2*evalQPoly rf1524.irrational a)/evalQPoly rf1524.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1524,rf1524]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-3/280 : ℚ)*Polynomial.X^0 + Polynomial.C (39/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-839/280 : ℚ)*Polynomial.X^2 + Polynomial.C (634/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-9559/140 : ℚ)*Polynomial.X^4 + Polynomial.C (11579/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-35379/140 : ℚ)*Polynomial.X^6 + Polynomial.C (7804/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-22719/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-3349/140 : ℚ)*Polynomial.X^9 + Polynomial.C (891/40 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1539.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1539.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1539.rational a+Real.sqrt 2*evalQPoly rf1539.irrational a)/evalQPoly rf1539.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1539,rf1524]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-171/70 : ℚ)*Polynomial.X^2 + Polynomial.C (57/5 : ℚ)*Polynomial.X^3 + Polynomial.C (-409/14 : ℚ)*Polynomial.X^4 + Polynomial.C (976/35 : ℚ)*Polynomial.X^5 + Polynomial.C (3791/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1389/7 : ℚ)*Polynomial.X^7 + Polynomial.C (1187/5 : ℚ)*Polynomial.X^8 + Polynomial.C (-112 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1568.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1568.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1568.rational a+Real.sqrt 2*evalQPoly rf1568.irrational a)/evalQPoly rf1568.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1568,rf1524]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (33/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-123/28 : ℚ)*Polynomial.X^2 + Polynomial.C (219/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-4001/70 : ℚ)*Polynomial.X^4 + Polynomial.C (415/14 : ℚ)*Polynomial.X^5 + Polynomial.C (21853/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-80033/70 : ℚ)*Polynomial.X^7 + Polynomial.C (272717/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-61508/35 : ℚ)*Polynomial.X^9 + Polynomial.C (14099/20 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1553.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1553.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1553.rational a+Real.sqrt 2*evalQPoly rf1553.irrational a)/evalQPoly rf1553.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1553,rf1524]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-36/35 : ℚ)*Polynomial.X^2 + Polynomial.C (349/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-268/5 : ℚ)*Polynomial.X^4 + Polynomial.C (6178/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-12764/35 : ℚ)*Polynomial.X^6 + Polynomial.C (16183/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-11644/35 : ℚ)*Polynomial.X^8 + Polynomial.C (1031/10 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1581.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1581.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1581.rational a+Real.sqrt 2*evalQPoly rf1581.irrational a)/evalQPoly rf1581.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1581,rf1524]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/10 : ℚ)*Polynomial.X^1 + Polynomial.C (87/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-141/14 : ℚ)*Polynomial.X^3 + Polynomial.C (91/5 : ℚ)*Polynomial.X^4 + Polynomial.C (209/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-2453/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1123/10 : ℚ)*Polynomial.X^7 + Polynomial.C (-133/2 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf1610.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1610.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1610.rational a+Real.sqrt 2*evalQPoly rf1610.irrational a)/evalQPoly rf1610.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1610,rf1524]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/140 : ℚ)*Polynomial.X^1 + Polynomial.C (26/35 : ℚ)*Polynomial.X^2 + Polynomial.C (9/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-2019/70 : ℚ)*Polynomial.X^4 + Polynomial.C (753/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-14228/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1255/2 : ℚ)*Polynomial.X^7 + Polynomial.C (-75059/140 : ℚ)*Polynomial.X^8 + Polynomial.C (4057/20 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1595.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1595.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1595.rational a+Real.sqrt 2*evalQPoly rf1595.irrational a)/evalQPoly rf1595.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1595,rf1524]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (3/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-18/35 : ℚ)*Polynomial.X^1 + Polynomial.C (349/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-134/5 : ℚ)*Polynomial.X^3 + Polynomial.C (3089/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-6382/35 : ℚ)*Polynomial.X^5 + Polynomial.C (16183/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-5822/35 : ℚ)*Polynomial.X^7 + Polynomial.C (1031/20 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf1624.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1624.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1624.rational a+Real.sqrt 2*evalQPoly rf1624.irrational a)/evalQPoly rf1624.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1624,rf1524]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/35 : ℚ)*Polynomial.X^0 + Polynomial.C (-37/70 : ℚ)*Polynomial.X^1 + Polynomial.C (136/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-981/70 : ℚ)*Polynomial.X^3 + Polynomial.C (153/7 : ℚ)*Polynomial.X^4 + Polynomial.C (149/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-3354/35 : ℚ)*Polynomial.X^6 + Polynomial.C (9729/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-76 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf1638.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1638.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1638.rational a+Real.sqrt 2*evalQPoly rf1638.irrational a)/evalQPoly rf1638.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1638,rf1524]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd025
