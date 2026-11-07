import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd055
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1939.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/280 : ℚ)*Polynomial.X^1 + Polynomial.C (19/280 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/2 : ℚ)*Polynomial.X^3 + Polynomial.C (117/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-261/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-321/140 : ℚ)*Polynomial.X^6 + Polynomial.C (95/14 : ℚ)*Polynomial.X^7 + Polynomial.C (-633/70 : ℚ)*Polynomial.X^8 + Polynomial.C (3131/280 : ℚ)*Polynomial.X^9 + Polynomial.C (447/280 : ℚ)*Polynomial.X^10 + Polynomial.C (-74/35 : ℚ)*Polynomial.X^11
theorem eval0 (a : ℝ) (h : rf1939.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1939.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1939.rational a+Real.sqrt 2*evalQPoly rf1939.irrational a)/evalQPoly rf1939.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1939,rf1939]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-93/280 : ℚ)*Polynomial.X^2 + Polynomial.C (11/14 : ℚ)*Polynomial.X^3 + Polynomial.C (-43/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-111/70 : ℚ)*Polynomial.X^5 + Polynomial.C (393/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-243/70 : ℚ)*Polynomial.X^7 + Polynomial.C (871/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^9 + Polynomial.C (-261/280 : ℚ)*Polynomial.X^10
theorem eval1 (a : ℝ) (h : rf1958.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1958.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1958.rational a+Real.sqrt 2*evalQPoly rf1958.irrational a)/evalQPoly rf1958.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1958,rf1939]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (3/56 : ℚ)*Polynomial.X^1 + Polynomial.C (-19/70 : ℚ)*Polynomial.X^2 + Polynomial.C (31/70 : ℚ)*Polynomial.X^3 + Polynomial.C (51/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-45/28 : ℚ)*Polynomial.X^5 + Polynomial.C (143/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-139/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-277/280 : ℚ)*Polynomial.X^8 + Polynomial.C (1/8 : ℚ)*Polynomial.X^9
theorem eval2 (a : ℝ) (h : rf1995.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1995.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1995.rational a+Real.sqrt 2*evalQPoly rf1995.irrational a)/evalQPoly rf1995.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1995,rf1939]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (2/35 : ℚ)*Polynomial.X^1 + Polynomial.C (-89/280 : ℚ)*Polynomial.X^2 + Polynomial.C (39/70 : ℚ)*Polynomial.X^3 + Polynomial.C (167/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-437/70 : ℚ)*Polynomial.X^5 + Polynomial.C (1023/140 : ℚ)*Polynomial.X^6 + Polynomial.C (257/70 : ℚ)*Polynomial.X^7 + Polynomial.C (-841/56 : ℚ)*Polynomial.X^8 + Polynomial.C (1769/70 : ℚ)*Polynomial.X^9 + Polynomial.C (-2053/280 : ℚ)*Polynomial.X^10
theorem eval3 (a : ℝ) (h : rf1976.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1976.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1976.rational a+Real.sqrt 2*evalQPoly rf1976.irrational a)/evalQPoly rf1976.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1976,rf1939]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/5 : ℚ)*Polynomial.X^2 + Polynomial.C (34/35 : ℚ)*Polynomial.X^3 + Polynomial.C (-61/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-1/35 : ℚ)*Polynomial.X^5 + Polynomial.C (139/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-58/7 : ℚ)*Polynomial.X^7 + Polynomial.C (281/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-191/70 : ℚ)*Polynomial.X^9
theorem eval4 (a : ℝ) (h : rf2013.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2013.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2013.rational a+Real.sqrt 2*evalQPoly rf2013.irrational a)/evalQPoly rf2013.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2013,rf1939]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/70 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^2 + Polynomial.C (69/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-67/70 : ℚ)*Polynomial.X^4 + Polynomial.C (-193/70 : ℚ)*Polynomial.X^5 + Polynomial.C (319/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-277/70 : ℚ)*Polynomial.X^7 + Polynomial.C (1/2 : ℚ)*Polynomial.X^8
theorem eval5 (a : ℝ) (h : rf2050.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2050.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2050.rational a+Real.sqrt 2*evalQPoly rf2050.irrational a)/evalQPoly rf2050.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2050,rf1939]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/70 : ℚ)*Polynomial.X^2 + Polynomial.C (109/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-17/4 : ℚ)*Polynomial.X^4 + Polynomial.C (193/140 : ℚ)*Polynomial.X^5 + Polynomial.C (107/10 : ℚ)*Polynomial.X^6 + Polynomial.C (-1321/70 : ℚ)*Polynomial.X^7 + Polynomial.C (3029/280 : ℚ)*Polynomial.X^8 + Polynomial.C (181/280 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf2031.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2031.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2031.rational a+Real.sqrt 2*evalQPoly rf2031.irrational a)/evalQPoly rf2031.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2031,rf1939]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (16/35 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-59/70 : ℚ)*Polynomial.X^4 + Polynomial.C (163/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-76/35 : ℚ)*Polynomial.X^6 + Polynomial.C (-51/70 : ℚ)*Polynomial.X^7 + Polynomial.C (229/140 : ℚ)*Polynomial.X^8
theorem eval7 (a : ℝ) (h : rf2068.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2068.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2068.rational a+Real.sqrt 2*evalQPoly rf2068.irrational a)/evalQPoly rf2068.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2068,rf1939]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/140 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/10 : ℚ)*Polynomial.X^1 + Polynomial.C (33/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-51/70 : ℚ)*Polynomial.X^3 + Polynomial.C (-22/35 : ℚ)*Polynomial.X^4 + Polynomial.C (263/70 : ℚ)*Polynomial.X^5 + Polynomial.C (-377/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-173/70 : ℚ)*Polynomial.X^7 + Polynomial.C (13/4 : ℚ)*Polynomial.X^8
theorem eval8 (a : ℝ) (h : rf2084.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2084.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2084.rational a+Real.sqrt 2*evalQPoly rf2084.irrational a)/evalQPoly rf2084.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2084,rf1939]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd055
