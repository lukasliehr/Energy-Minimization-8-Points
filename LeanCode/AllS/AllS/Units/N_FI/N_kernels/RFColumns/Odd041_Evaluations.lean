import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd041
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1925.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/70 : ℚ)*Polynomial.X^3 + Polynomial.C (135/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-4021/140 : ℚ)*Polynomial.X^5 + Polynomial.C (13689/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-27163/140 : ℚ)*Polynomial.X^7 + Polynomial.C (28829/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-9411/140 : ℚ)*Polynomial.X^9 + Polynomial.C (-1517/20 : ℚ)*Polynomial.X^10 + Polynomial.C (1483/20 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1925.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1925.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1925.rational a+Real.sqrt 2*evalQPoly rf1925.irrational a)/evalQPoly rf1925.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1925,rf1925]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (9/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/35 : ℚ)*Polynomial.X^2 + Polynomial.C (11/2 : ℚ)*Polynomial.X^3 + Polynomial.C (-688/35 : ℚ)*Polynomial.X^4 + Polynomial.C (663/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-5053/70 : ℚ)*Polynomial.X^6 + Polynomial.C (859/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-2431/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-482/35 : ℚ)*Polynomial.X^9 + Polynomial.C (97/10 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1944.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1944.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1944.rational a+Real.sqrt 2*evalQPoly rf1944.irrational a)/evalQPoly rf1944.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1944,rf1925]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (4/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-111/140 : ℚ)*Polynomial.X^2 + Polynomial.C (13/4 : ℚ)*Polynomial.X^3 + Polynomial.C (-1147/140 : ℚ)*Polynomial.X^4 + Polynomial.C (1209/140 : ℚ)*Polynomial.X^5 + Polynomial.C (2039/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-8247/140 : ℚ)*Polynomial.X^7 + Polynomial.C (363/5 : ℚ)*Polynomial.X^8 + Polynomial.C (-147/4 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1981.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1981.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1981.rational a+Real.sqrt 2*evalQPoly rf1981.irrational a)/evalQPoly rf1981.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1981,rf1925]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (23/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-213/140 : ℚ)*Polynomial.X^2 + Polynomial.C (258/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-663/35 : ℚ)*Polynomial.X^4 + Polynomial.C (821/70 : ℚ)*Polynomial.X^5 + Polynomial.C (634/7 : ℚ)*Polynomial.X^6 + Polynomial.C (-11988/35 : ℚ)*Polynomial.X^7 + Polynomial.C (82357/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-14981/28 : ℚ)*Polynomial.X^9 + Polynomial.C (4547/20 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1962.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1962.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1962.rational a+Real.sqrt 2*evalQPoly rf1962.irrational a)/evalQPoly rf1962.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1962,rf1925]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^2 + Polynomial.C (117/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-552/35 : ℚ)*Polynomial.X^4 + Polynomial.C (1759/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-3604/35 : ℚ)*Polynomial.X^6 + Polynomial.C (4491/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-3204/35 : ℚ)*Polynomial.X^8 + Polynomial.C (144/5 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf1999.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1999.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1999.rational a+Real.sqrt 2*evalQPoly rf1999.irrational a)/evalQPoly rf1999.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1999,rf1925]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (3/5 : ℚ)*Polynomial.X^2 + Polynomial.C (-213/70 : ℚ)*Polynomial.X^3 + Polynomial.C (213/35 : ℚ)*Polynomial.X^4 + Polynomial.C (39/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-747/35 : ℚ)*Polynomial.X^6 + Polynomial.C (327/10 : ℚ)*Polynomial.X^7 + Polynomial.C (-21 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf2036.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2036.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2036.rational a+Real.sqrt 2*evalQPoly rf2036.irrational a)/evalQPoly rf2036.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2036,rf1925]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (9/28 : ℚ)*Polynomial.X^2 + Polynomial.C (1/4 : ℚ)*Polynomial.X^3 + Polynomial.C (-1147/140 : ℚ)*Polynomial.X^4 + Polynomial.C (5981/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-471/4 : ℚ)*Polynomial.X^6 + Polynomial.C (5113/28 : ℚ)*Polynomial.X^7 + Polynomial.C (-10951/70 : ℚ)*Polynomial.X^8 + Polynomial.C (1241/20 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf2017.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2017.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2017.rational a+Real.sqrt 2*evalQPoly rf2017.irrational a)/evalQPoly rf2017.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2017,rf1925]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (117/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-276/35 : ℚ)*Polynomial.X^3 + Polynomial.C (1759/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-1802/35 : ℚ)*Polynomial.X^5 + Polynomial.C (4491/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-1602/35 : ℚ)*Polynomial.X^7 + Polynomial.C (72/5 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf2054.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2054.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2054.rational a+Real.sqrt 2*evalQPoly rf2054.irrational a)/evalQPoly rf2054.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2054,rf1925]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-8/35 : ℚ)*Polynomial.X^1 + Polynomial.C (51/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-163/35 : ℚ)*Polynomial.X^3 + Polynomial.C (33/5 : ℚ)*Polynomial.X^4 + Polynomial.C (148/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-1107/35 : ℚ)*Polynomial.X^6 + Polynomial.C (1583/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-53/2 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf2072.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2072.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2072.rational a+Real.sqrt 2*evalQPoly rf2072.irrational a)/evalQPoly rf2072.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2072,rf1925]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd041
