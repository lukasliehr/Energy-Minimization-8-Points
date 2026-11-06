import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even066
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1658.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/136 : ℚ)*Polynomial.X^1 + Polynomial.C (30/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-407/952 : ℚ)*Polynomial.X^3 + Polynomial.C (-857/476 : ℚ)*Polynomial.X^4 + Polynomial.C (-395/68 : ℚ)*Polynomial.X^5 + Polynomial.C (9476/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-119451/476 : ℚ)*Polynomial.X^7 + Polynomial.C (81563/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-25729/952 : ℚ)*Polynomial.X^9 + Polynomial.C (-67140/119 : ℚ)*Polynomial.X^10 + Polynomial.C (517117/952 : ℚ)*Polynomial.X^11 + Polynomial.C (11453/68 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1658.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1658.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1658.rational a+Real.sqrt 2*evalQPoly rf1658.irrational a)/evalQPoly rf1658.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1658,rf1658]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-25/476 : ℚ)*Polynomial.X^1 + Polynomial.C (363/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-405/119 : ℚ)*Polynomial.X^3 + Polynomial.C (95/34 : ℚ)*Polynomial.X^4 + Polynomial.C (2392/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-6738/119 : ℚ)*Polynomial.X^6 + Polynomial.C (215/34 : ℚ)*Polynomial.X^7 + Polynomial.C (38135/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-95927/476 : ℚ)*Polynomial.X^9 + Polynomial.C (-5221/68 : ℚ)*Polynomial.X^10 + Polynomial.C (11767/34 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1682.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1682.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1682.rational a+Real.sqrt 2*evalQPoly rf1682.irrational a)/evalQPoly rf1682.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1682,rf1658]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (5/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-83/68 : ℚ)*Polynomial.X^2 + Polynomial.C (1759/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-5779/238 : ℚ)*Polynomial.X^4 + Polynomial.C (6535/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-7858/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-2543/238 : ℚ)*Polynomial.X^7 + Polynomial.C (37307/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-99103/476 : ℚ)*Polynomial.X^9 + Polynomial.C (107/4 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1728.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1728.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1728.rational a+Real.sqrt 2*evalQPoly rf1728.irrational a)/evalQPoly rf1728.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1728,rf1658]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-6/7 : ℚ)*Polynomial.X^2 + Polynomial.C (538/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-258/17 : ℚ)*Polynomial.X^4 + Polynomial.C (4184/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-1650/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-13082/119 : ℚ)*Polynomial.X^7 + Polynomial.C (4074/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-217 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1797.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1797.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1797.rational a+Real.sqrt 2*evalQPoly rf1797.irrational a)/evalQPoly rf1797.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1797,rf1658]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (3/136 : ℚ)*Polynomial.X^0 + Polynomial.C (-55/136 : ℚ)*Polynomial.X^1 + Polynomial.C (2627/952 : ℚ)*Polynomial.X^2 + Polynomial.C (-8013/952 : ℚ)*Polynomial.X^3 + Polynomial.C (507/68 : ℚ)*Polynomial.X^4 + Polynomial.C (8707/476 : ℚ)*Polynomial.X^5 + Polynomial.C (-8633/476 : ℚ)*Polynomial.X^6 + Polynomial.C (-69469/476 : ℚ)*Polynomial.X^7 + Polynomial.C (446017/952 : ℚ)*Polynomial.X^8 + Polynomial.C (-462949/952 : ℚ)*Polynomial.X^9 + Polynomial.C (-125921/952 : ℚ)*Polynomial.X^10 + Polynomial.C (92705/136 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf1704.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1704.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1704.rational a+Real.sqrt 2*evalQPoly rf1704.irrational a)/evalQPoly rf1704.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1704,rf1658]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/476 : ℚ)*Polynomial.X^1 + Polynomial.C (137/476 : ℚ)*Polynomial.X^2 + Polynomial.C (-159/238 : ℚ)*Polynomial.X^3 + Polynomial.C (-1264/119 : ℚ)*Polynomial.X^4 + Polynomial.C (8571/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-20288/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2833/34 : ℚ)*Polynomial.X^7 + Polynomial.C (214199/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-479377/476 : ℚ)*Polynomial.X^9 + Polynomial.C (57801/68 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf1751.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1751.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1751.rational a+Real.sqrt 2*evalQPoly rf1751.irrational a)/evalQPoly rf1751.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1751,rf1658]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (-5/68 : ℚ)*Polynomial.X^0 + Polynomial.C (41/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-788/119 : ℚ)*Polynomial.X^2 + Polynomial.C (1803/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-4007/238 : ℚ)*Polynomial.X^4 + Polynomial.C (1786/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-294/17 : ℚ)*Polynomial.X^6 + Polynomial.C (1165/119 : ℚ)*Polynomial.X^7 + Polynomial.C (25961/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-213/2 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1819.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1819.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1819.rational a+Real.sqrt 2*evalQPoly rf1819.irrational a)/evalQPoly rf1819.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1819,rf1658]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (7/136 : ℚ)*Polynomial.X^0 + Polynomial.C (-15/17 : ℚ)*Polynomial.X^1 + Polynomial.C (747/136 : ℚ)*Polynomial.X^2 + Polynomial.C (-2049/119 : ℚ)*Polynomial.X^3 + Polynomial.C (13837/476 : ℚ)*Polynomial.X^4 + Polynomial.C (29/7 : ℚ)*Polynomial.X^5 + Polynomial.C (-73603/476 : ℚ)*Polynomial.X^6 + Polynomial.C (46077/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-492267/952 : ℚ)*Polynomial.X^8 + Polynomial.C (29856/119 : ℚ)*Polynomial.X^9 + Polynomial.C (-8769/136 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf1773.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1773.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1773.rational a+Real.sqrt 2*evalQPoly rf1773.irrational a)/evalQPoly rf1773.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1773,rf1658]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (5/119 : ℚ)*Polynomial.X^1 + Polynomial.C (-107/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-151/238 : ℚ)*Polynomial.X^3 + Polynomial.C (3649/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-9287/238 : ℚ)*Polynomial.X^5 + Polynomial.C (2447/238 : ℚ)*Polynomial.X^6 + Polynomial.C (23291/238 : ℚ)*Polynomial.X^7 + Polynomial.C (-7411/34 : ℚ)*Polynomial.X^8 + Polynomial.C (2527/34 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf1842.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1842.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1842.rational a+Real.sqrt 2*evalQPoly rf1842.irrational a)/evalQPoly rf1842.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1842,rf1658]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-7/68 : ℚ)*Polynomial.X^0 + Polynomial.C (55/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-1899/238 : ℚ)*Polynomial.X^2 + Polynomial.C (2865/238 : ℚ)*Polynomial.X^3 + Polynomial.C (1608/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-19413/238 : ℚ)*Polynomial.X^5 + Polynomial.C (36115/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-33821/238 : ℚ)*Polynomial.X^7 + Polynomial.C (263/4 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf1888.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1888.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1888.rational a+Real.sqrt 2*evalQPoly rf1888.irrational a)/evalQPoly rf1888.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1888,rf1658]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-33/68 : ℚ)*Polynomial.X^1 + Polynomial.C (43/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-592/119 : ℚ)*Polynomial.X^3 + Polynomial.C (184/119 : ℚ)*Polynomial.X^4 + Polynomial.C (3973/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-6373/119 : ℚ)*Polynomial.X^6 + Polynomial.C (5570/119 : ℚ)*Polynomial.X^7 + Polynomial.C (1977/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-13437/68 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf1864.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1864.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1864.rational a+Real.sqrt 2*evalQPoly rf1864.irrational a)/evalQPoly rf1864.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1864,rf1658]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (1/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-33/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-355/238 : ℚ)*Polynomial.X^3 + Polynomial.C (297/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-509/14 : ℚ)*Polynomial.X^5 + Polynomial.C (-3399/238 : ℚ)*Polynomial.X^6 + Polynomial.C (3609/34 : ℚ)*Polynomial.X^7 + Polynomial.C (-13629/68 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf1911.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1911.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1911.rational a+Real.sqrt 2*evalQPoly rf1911.irrational a)/evalQPoly rf1911.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1911,rf1658]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even066
