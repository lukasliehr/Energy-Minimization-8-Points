import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even073
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1665.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/238 : ℚ)*Polynomial.X^1 + Polynomial.C (9/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-127/238 : ℚ)*Polynomial.X^3 + Polynomial.C (235/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-450/119 : ℚ)*Polynomial.X^5 + Polynomial.C (130/119 : ℚ)*Polynomial.X^6 + Polynomial.C (68/7 : ℚ)*Polynomial.X^7 + Polynomial.C (-1954/119 : ℚ)*Polynomial.X^8 + Polynomial.C (3341/238 : ℚ)*Polynomial.X^9 + Polynomial.C (-3811/119 : ℚ)*Polynomial.X^10 + Polynomial.C (8943/238 : ℚ)*Polynomial.X^11 + Polynomial.C (1679/119 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1665.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1665.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1665.rational a+Real.sqrt 2*evalQPoly rf1665.irrational a)/evalQPoly rf1665.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1665,rf1665]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/476 : ℚ)*Polynomial.X^1 + Polynomial.C (13/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-37/238 : ℚ)*Polynomial.X^3 + Polynomial.C (67/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-249/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-311/238 : ℚ)*Polynomial.X^6 + Polynomial.C (1062/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-109/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-9309/476 : ℚ)*Polynomial.X^9 + Polynomial.C (6529/476 : ℚ)*Polynomial.X^10 + Polynomial.C (983/34 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1689.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1689.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1689.rational a+Real.sqrt 2*evalQPoly rf1689.irrational a)/evalQPoly rf1689.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1689,rf1665]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/14 : ℚ)*Polynomial.X^2 + Polynomial.C (150/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-363/119 : ℚ)*Polynomial.X^4 + Polynomial.C (157/119 : ℚ)*Polynomial.X^5 + Polynomial.C (914/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-1674/119 : ℚ)*Polynomial.X^7 + Polynomial.C (1563/119 : ℚ)*Polynomial.X^8 + Polynomial.C (-2965/238 : ℚ)*Polynomial.X^9 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1735.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1735.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1735.rational a+Real.sqrt 2*evalQPoly rf1735.irrational a)/evalQPoly rf1735.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1735,rf1665]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (3/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-40/119 : ℚ)*Polynomial.X^4 + Polynomial.C (155/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-216/119 : ℚ)*Polynomial.X^6 + Polynomial.C (9/119 : ℚ)*Polynomial.X^7 + Polynomial.C (64/7 : ℚ)*Polynomial.X^8 + Polynomial.C (-17 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1804.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1804.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1804.rational a+Real.sqrt 2*evalQPoly rf1804.irrational a)/evalQPoly rf1804.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1804,rf1665]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-10/119 : ℚ)*Polynomial.X^1 + Polynomial.C (82/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-729/238 : ℚ)*Polynomial.X^3 + Polynomial.C (54/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-1010/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-1107/119 : ℚ)*Polynomial.X^6 + Polynomial.C (5665/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-15965/238 : ℚ)*Polynomial.X^8 + Polynomial.C (4832/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-481/17 : ℚ)*Polynomial.X^10 + Polynomial.C (12879/238 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf1711.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1711.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1711.rational a+Real.sqrt 2*evalQPoly rf1711.irrational a)/evalQPoly rf1711.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1711,rf1665]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/476 : ℚ)*Polynomial.X^1 + Polynomial.C (69/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-46/119 : ℚ)*Polynomial.X^3 + Polynomial.C (6/17 : ℚ)*Polynomial.X^4 + Polynomial.C (319/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-856/119 : ℚ)*Polynomial.X^6 + Polynomial.C (1844/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-1985/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-3055/68 : ℚ)*Polynomial.X^9 + Polynomial.C (4725/68 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf1758.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1758.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1758.rational a+Real.sqrt 2*evalQPoly rf1758.irrational a)/evalQPoly rf1758.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1758,rf1665]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-3/238 : ℚ)*Polynomial.X^0 + Polynomial.C (55/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-185/119 : ℚ)*Polynomial.X^2 + Polynomial.C (34/7 : ℚ)*Polynomial.X^3 + Polynomial.C (-100/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-743/119 : ℚ)*Polynomial.X^5 + Polynomial.C (3441/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-4302/119 : ℚ)*Polynomial.X^7 + Polynomial.C (861/34 : ℚ)*Polynomial.X^8 + Polynomial.C (-193/14 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1826.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1826.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1826.rational a+Real.sqrt 2*evalQPoly rf1826.irrational a)/evalQPoly rf1826.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1826,rf1665]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/119 : ℚ)*Polynomial.X^1 + Polynomial.C (135/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-67/17 : ℚ)*Polynomial.X^3 + Polynomial.C (808/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-331/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-244/17 : ℚ)*Polynomial.X^6 + Polynomial.C (5529/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-8697/119 : ℚ)*Polynomial.X^8 + Polynomial.C (5402/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-1675/119 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf1780.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1780.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1780.rational a+Real.sqrt 2*evalQPoly rf1780.irrational a)/evalQPoly rf1780.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1780,rf1665]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/238 : ℚ)*Polynomial.X^1 + Polynomial.C (11/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/238 : ℚ)*Polynomial.X^3 + Polynomial.C (33/238 : ℚ)*Polynomial.X^4 + Polynomial.C (87/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-59/238 : ℚ)*Polynomial.X^6 + Polynomial.C (63/34 : ℚ)*Polynomial.X^7 + Polynomial.C (-167/34 : ℚ)*Polynomial.X^8 + Polynomial.C (-133/17 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf1849.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1849.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1849.rational a+Real.sqrt 2*evalQPoly rf1849.irrational a)/evalQPoly rf1849.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1849,rf1665]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-2/119 : ℚ)*Polynomial.X^0 + Polynomial.C (5/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-31/17 : ℚ)*Polynomial.X^2 + Polynomial.C (583/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-421/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-1383/119 : ℚ)*Polynomial.X^5 + Polynomial.C (3613/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-3363/119 : ℚ)*Polynomial.X^7 + Polynomial.C (83/7 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf1895.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1895.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1895.rational a+Real.sqrt 2*evalQPoly rf1895.irrational a)/evalQPoly rf1895.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1895,rf1665]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-19/238 : ℚ)*Polynomial.X^1 + Polynomial.C (57/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-104/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-174/119 : ℚ)*Polynomial.X^4 + Polynomial.C (789/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-457/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-108/17 : ℚ)*Polynomial.X^7 + Polynomial.C (1531/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-617/34 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf1871.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1871.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1871.rational a+Real.sqrt 2*evalQPoly rf1871.irrational a)/evalQPoly rf1871.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1871,rf1665]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (3/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/14 : ℚ)*Polynomial.X^3 + Polynomial.C (5/14 : ℚ)*Polynomial.X^4 + Polynomial.C (-463/238 : ℚ)*Polynomial.X^5 + Polynomial.C (579/119 : ℚ)*Polynomial.X^6 + Polynomial.C (989/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-1671/68 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf1918.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1918.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1918.rational a+Real.sqrt 2*evalQPoly rf1918.irrational a)/evalQPoly rf1918.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1918,rf1665]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even073
