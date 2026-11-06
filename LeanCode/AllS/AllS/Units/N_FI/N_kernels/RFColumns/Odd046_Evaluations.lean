import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd046
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1930.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (13/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/10 : ℚ)*Polynomial.X^3 + Polynomial.C (137/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-25/14 : ℚ)*Polynomial.X^5 + Polynomial.C (143/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-513/70 : ℚ)*Polynomial.X^7 + Polynomial.C (439/70 : ℚ)*Polynomial.X^8 + Polynomial.C (167/35 : ℚ)*Polynomial.X^9 + Polynomial.C (2/7 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1930.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1930.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1930.rational a+Real.sqrt 2*evalQPoly rf1930.irrational a)/evalQPoly rf1930.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1930,rf1930]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-5/14 : ℚ)*Polynomial.X^2 + Polynomial.C (3/5 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/5 : ℚ)*Polynomial.X^4 + Polynomial.C (11/5 : ℚ)*Polynomial.X^5 + Polynomial.C (-53/10 : ℚ)*Polynomial.X^6 + Polynomial.C (129/35 : ℚ)*Polynomial.X^7 + Polynomial.C (11/20 : ℚ)*Polynomial.X^8 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1949.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1949.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1949.rational a+Real.sqrt 2*evalQPoly rf1949.irrational a)/evalQPoly rf1949.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1949,rf1930]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (3/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/35 : ℚ)*Polynomial.X^2 + Polynomial.C (6/35 : ℚ)*Polynomial.X^3 + Polynomial.C (69/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-43/35 : ℚ)*Polynomial.X^5 + Polynomial.C (19/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-46/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1986.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1986.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1986.rational a+Real.sqrt 2*evalQPoly rf1986.irrational a)/evalQPoly rf1986.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1986,rf1930]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/28 : ℚ)*Polynomial.X^2 + Polynomial.C (-5/28 : ℚ)*Polynomial.X^3 + Polynomial.C (197/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-63/20 : ℚ)*Polynomial.X^5 + Polynomial.C (145/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-395/28 : ℚ)*Polynomial.X^7 + Polynomial.C (2923/140 : ℚ)*Polynomial.X^8 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1967.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1967.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1967.rational a+Real.sqrt 2*evalQPoly rf1967.irrational a)/evalQPoly rf1967.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1967,rf1930]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/7 : ℚ)*Polynomial.X^2 + Polynomial.C (32/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-41/35 : ℚ)*Polynomial.X^4 + Polynomial.C (69/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-216/35 : ℚ)*Polynomial.X^6 + Polynomial.C (50/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-17/7 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2004.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2004.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2004.rational a+Real.sqrt 2*evalQPoly rf2004.irrational a)/evalQPoly rf2004.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2004,rf1930]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (11/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-17/140 : ℚ)*Polynomial.X^3 + Polynomial.C (37/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-59/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-59/28 : ℚ)*Polynomial.X^6 + Polynomial.C (-5/4 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2041.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2041.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2041.rational a+Real.sqrt 2*evalQPoly rf2041.irrational a)/evalQPoly rf2041.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2041,rf1930]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/35 : ℚ)*Polynomial.X^2 + Polynomial.C (11/10 : ℚ)*Polynomial.X^3 + Polynomial.C (-131/70 : ℚ)*Polynomial.X^4 + Polynomial.C (23/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-216/35 : ℚ)*Polynomial.X^6 + Polynomial.C (627/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-47/28 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2022.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2022.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2022.rational a+Real.sqrt 2*evalQPoly rf2022.irrational a)/evalQPoly rf2022.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2022,rf1930]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/7 : ℚ)*Polynomial.X^1 + Polynomial.C (31/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/35 : ℚ)*Polynomial.X^3 + Polynomial.C (51/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-17/5 : ℚ)*Polynomial.X^5 + Polynomial.C (317/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-12/7 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2059.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2059.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2059.rational a+Real.sqrt 2*evalQPoly rf2059.irrational a)/evalQPoly rf2059.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2059,rf1930]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/140 : ℚ)*Polynomial.X^1 + Polynomial.C (3/28 : ℚ)*Polynomial.X^2 + Polynomial.C (41/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-11/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-79/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-3/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2077.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2077.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2077.rational a+Real.sqrt 2*evalQPoly rf2077.irrational a)/evalQPoly rf2077.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2077,rf1930]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd046
