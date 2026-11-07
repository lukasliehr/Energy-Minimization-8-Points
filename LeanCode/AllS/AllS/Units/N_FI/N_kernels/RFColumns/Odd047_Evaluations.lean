import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd047
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1931.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-17/280 : ℚ)*Polynomial.X^1 + Polynomial.C (53/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-93/28 : ℚ)*Polynomial.X^3 + Polynomial.C (27/5 : ℚ)*Polynomial.X^4 + Polynomial.C (41/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-507/70 : ℚ)*Polynomial.X^6 + Polynomial.C (-341/20 : ℚ)*Polynomial.X^7 + Polynomial.C (1482/35 : ℚ)*Polynomial.X^8 + Polynomial.C (-3439/280 : ℚ)*Polynomial.X^9 + Polynomial.C (-468/35 : ℚ)*Polynomial.X^10
theorem eval0 (a : ℝ) (h : rf1931.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1931.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1931.rational a+Real.sqrt 2*evalQPoly rf1931.irrational a)/evalQPoly rf1931.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1931,rf1931]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (-1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (11/40 : ℚ)*Polynomial.X^1 + Polynomial.C (-67/70 : ℚ)*Polynomial.X^2 + Polynomial.C (31/35 : ℚ)*Polynomial.X^3 + Polynomial.C (13/28 : ℚ)*Polynomial.X^4 + Polynomial.C (603/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-249/14 : ℚ)*Polynomial.X^6 + Polynomial.C (641/35 : ℚ)*Polynomial.X^7 + Polynomial.C (-187/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-1347/280 : ℚ)*Polynomial.X^9
theorem eval1 (a : ℝ) (h : rf1950.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1950.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1950.rational a+Real.sqrt 2*evalQPoly rf1950.irrational a)/evalQPoly rf1950.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1950,rf1931]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (-1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (2/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-27/28 : ℚ)*Polynomial.X^2 + Polynomial.C (3/14 : ℚ)*Polynomial.X^3 + Polynomial.C (136/35 : ℚ)*Polynomial.X^4 + Polynomial.C (-157/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-41/28 : ℚ)*Polynomial.X^6 + Polynomial.C (27/14 : ℚ)*Polynomial.X^7 + Polynomial.C (5/8 : ℚ)*Polynomial.X^8
theorem eval2 (a : ℝ) (h : rf1987.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1987.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1987.rational a+Real.sqrt 2*evalQPoly rf1987.irrational a)/evalQPoly rf1987.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1987,rf1931]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (3/280 : ℚ)*Polynomial.X^0 + Polynomial.C (-37/280 : ℚ)*Polynomial.X^1 + Polynomial.C (57/70 : ℚ)*Polynomial.X^2 + Polynomial.C (-69/20 : ℚ)*Polynomial.X^3 + Polynomial.C (1089/140 : ℚ)*Polynomial.X^4 + Polynomial.C (-88/35 : ℚ)*Polynomial.X^5 + Polynomial.C (-223/14 : ℚ)*Polynomial.X^6 + Polynomial.C (-19/20 : ℚ)*Polynomial.X^7 + Polynomial.C (16707/280 : ℚ)*Polynomial.X^8 + Polynomial.C (-14731/280 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1968.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1968.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1968.rational a+Real.sqrt 2*evalQPoly rf1968.irrational a)/evalQPoly rf1968.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1968,rf1931]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (13/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-23/28 : ℚ)*Polynomial.X^2 + Polynomial.C (261/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/140 : ℚ)*Polynomial.X^4 + Polynomial.C (79/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-2657/140 : ℚ)*Polynomial.X^6 + Polynomial.C (5151/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-2729/140 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf2005.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2005.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf2005.rational a+Real.sqrt 2*evalQPoly rf2005.irrational a)/evalQPoly rf2005.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf2005,rf1931]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/28 : ℚ)*Polynomial.X^0 + Polynomial.C (3/7 : ℚ)*Polynomial.X^1 + Polynomial.C (-223/140 : ℚ)*Polynomial.X^2 + Polynomial.C (67/70 : ℚ)*Polynomial.X^3 + Polynomial.C (153/28 : ℚ)*Polynomial.X^4 + Polynomial.C (-304/35 : ℚ)*Polynomial.X^5 + Polynomial.C (27/28 : ℚ)*Polynomial.X^6 + Polynomial.C (5/2 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf2042.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2042.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf2042.rational a+Real.sqrt 2*evalQPoly rf2042.irrational a)/evalQPoly rf2042.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf2042,rf1931]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/40 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/140 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/70 : ℚ)*Polynomial.X^2 + Polynomial.C (499/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-87/20 : ℚ)*Polynomial.X^4 + Polynomial.C (-157/140 : ℚ)*Polynomial.X^5 + Polynomial.C (-603/70 : ℚ)*Polynomial.X^6 + Polynomial.C (4349/140 : ℚ)*Polynomial.X^7 + Polynomial.C (-6613/280 : ℚ)*Polynomial.X^8
theorem eval6 (a : ℝ) (h : rf2023.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2023.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf2023.rational a+Real.sqrt 2*evalQPoly rf2023.irrational a)/evalQPoly rf2023.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf2023,rf1931]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/20 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/20 : ℚ)*Polynomial.X^1 + Polynomial.C (149/140 : ℚ)*Polynomial.X^2 + Polynomial.C (-13/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/20 : ℚ)*Polynomial.X^4 + Polynomial.C (-1233/140 : ℚ)*Polynomial.X^5 + Polynomial.C (2507/140 : ℚ)*Polynomial.X^6 + Polynomial.C (-1347/140 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf2060.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2060.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf2060.rational a+Real.sqrt 2*evalQPoly rf2060.irrational a)/evalQPoly rf2060.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf2060,rf1931]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (1/70 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/28 : ℚ)*Polynomial.X^1 + Polynomial.C (1/70 : ℚ)*Polynomial.X^2 + Polynomial.C (149/140 : ℚ)*Polynomial.X^3 + Polynomial.C (-7/10 : ℚ)*Polynomial.X^4 + Polynomial.C (-81/28 : ℚ)*Polynomial.X^5 + Polynomial.C (19/14 : ℚ)*Polynomial.X^6 + Polynomial.C (5/4 : ℚ)*Polynomial.X^7
theorem eval8 (a : ℝ) (h : rf2078.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf2078.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf2078.rational a+Real.sqrt 2*evalQPoly rf2078.irrational a)/evalQPoly rf2078.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf2078,rf1931]
  all_goals ring
#print axioms eval8


end Blueprint.Thomson.Finite.RFColumnProofs.Odd047
