import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even076
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1668.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/952 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/476 : ℚ)*Polynomial.X^2 + Polynomial.C (195/952 : ℚ)*Polynomial.X^3 + Polynomial.C (-65/68 : ℚ)*Polynomial.X^4 + Polynomial.C (67/28 : ℚ)*Polynomial.X^5 + Polynomial.C (-521/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-1843/476 : ℚ)*Polynomial.X^7 + Polynomial.C (2721/238 : ℚ)*Polynomial.X^8 + Polynomial.C (-657/136 : ℚ)*Polynomial.X^9 + Polynomial.C (-3867/476 : ℚ)*Polynomial.X^10 + Polynomial.C (1331/952 : ℚ)*Polynomial.X^11 + Polynomial.C (1149/476 : ℚ)*Polynomial.X^12
theorem eval0 (a : ℝ) (h : rf1668.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1668.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1668.rational a+Real.sqrt 2*evalQPoly rf1668.irrational a)/evalQPoly rf1668.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1668,rf1668]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (2/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-31/119 : ℚ)*Polynomial.X^5 + Polynomial.C (157/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-256/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-316/119 : ℚ)*Polynomial.X^8 + Polynomial.C (207/17 : ℚ)*Polynomial.X^9 + Polynomial.C (-835/119 : ℚ)*Polynomial.X^10 + Polynomial.C (-134/17 : ℚ)*Polynomial.X^11
theorem eval1 (a : ℝ) (h : rf1692.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1692.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1692.rational a+Real.sqrt 2*evalQPoly rf1692.irrational a)/evalQPoly rf1692.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1692,rf1668]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/238 : ℚ)*Polynomial.X^1 + Polynomial.C (19/238 : ℚ)*Polynomial.X^2 + Polynomial.C (-66/119 : ℚ)*Polynomial.X^3 + Polynomial.C (12/7 : ℚ)*Polynomial.X^4 + Polynomial.C (-202/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-20/7 : ℚ)*Polynomial.X^6 + Polynomial.C (888/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-558/119 : ℚ)*Polynomial.X^8 + Polynomial.C (233/238 : ℚ)*Polynomial.X^9 + Polynomial.C (9/14 : ℚ)*Polynomial.X^10
theorem eval2 (a : ℝ) (h : rf1738.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1738.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1738.rational a+Real.sqrt 2*evalQPoly rf1738.irrational a)/evalQPoly rf1738.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1738,rf1668]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/119 : ℚ)*Polynomial.X^4 + Polynomial.C (9/119 : ℚ)*Polynomial.X^5 + Polynomial.C (6/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-18/17 : ℚ)*Polynomial.X^7 + Polynomial.C (11/119 : ℚ)*Polynomial.X^8 + Polynomial.C (3 : ℚ)*Polynomial.X^9
theorem eval3 (a : ℝ) (h : rf1807.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1807.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1807.rational a+Real.sqrt 2*evalQPoly rf1807.irrational a)/evalQPoly rf1807.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1807,rf1668]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/952 : ℚ)*Polynomial.X^0 + Polynomial.C (25/952 : ℚ)*Polynomial.X^1 + Polynomial.C (-253/952 : ℚ)*Polynomial.X^2 + Polynomial.C (1341/952 : ℚ)*Polynomial.X^3 + Polynomial.C (-1943/476 : ℚ)*Polynomial.X^4 + Polynomial.C (2455/476 : ℚ)*Polynomial.X^5 + Polynomial.C (2137/476 : ℚ)*Polynomial.X^6 + Polynomial.C (-1735/68 : ℚ)*Polynomial.X^7 + Polynomial.C (4457/136 : ℚ)*Polynomial.X^8 + Polynomial.C (-519/56 : ℚ)*Polynomial.X^9 + Polynomial.C (-13157/952 : ℚ)*Polynomial.X^10 + Polynomial.C (4565/952 : ℚ)*Polynomial.X^11
theorem eval4 (a : ℝ) (h : rf1714.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1714.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1714.rational a+Real.sqrt 2*evalQPoly rf1714.irrational a)/evalQPoly rf1714.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1714,rf1668]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (1/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^5 + Polynomial.C (207/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-536/119 : ℚ)*Polynomial.X^7 + Polynomial.C (39/119 : ℚ)*Polynomial.X^8 + Polynomial.C (284/17 : ℚ)*Polynomial.X^9 + Polynomial.C (-385/17 : ℚ)*Polynomial.X^10
theorem eval5 (a : ℝ) (h : rf1761.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1761.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1761.rational a+Real.sqrt 2*evalQPoly rf1761.irrational a)/evalQPoly rf1761.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1761,rf1668]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/238 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/34 : ℚ)*Polynomial.X^1 + Polynomial.C (12/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-320/119 : ℚ)*Polynomial.X^3 + Polynomial.C (522/119 : ℚ)*Polynomial.X^4 + Polynomial.C (162/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-1910/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2722/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-2993/238 : ℚ)*Polynomial.X^8 + Polynomial.C (29/14 : ℚ)*Polynomial.X^9
theorem eval6 (a : ℝ) (h : rf1829.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1829.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1829.rational a+Real.sqrt 2*evalQPoly rf1829.irrational a)/evalQPoly rf1829.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1829,rf1668]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-3/952 : ℚ)*Polynomial.X^0 + Polynomial.C (15/238 : ℚ)*Polynomial.X^1 + Polynomial.C (-465/952 : ℚ)*Polynomial.X^2 + Polynomial.C (229/119 : ℚ)*Polynomial.X^3 + Polynomial.C (-1861/476 : ℚ)*Polynomial.X^4 + Polynomial.C (249/119 : ℚ)*Polynomial.X^5 + Polynomial.C (4901/476 : ℚ)*Polynomial.X^6 + Polynomial.C (-3911/119 : ℚ)*Polynomial.X^7 + Polynomial.C (39901/952 : ℚ)*Polynomial.X^8 + Polynomial.C (-2781/238 : ℚ)*Polynomial.X^9 + Polynomial.C (-9033/952 : ℚ)*Polynomial.X^10
theorem eval7 (a : ℝ) (h : rf1783.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1783.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1783.rational a+Real.sqrt 2*evalQPoly rf1783.irrational a)/evalQPoly rf1783.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1783,rf1668]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/119 : ℚ)*Polynomial.X^4 + Polynomial.C (41/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-134/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-54/119 : ℚ)*Polynomial.X^7 + Polynomial.C (79/17 : ℚ)*Polynomial.X^8 + Polynomial.C (-21/17 : ℚ)*Polynomial.X^9
theorem eval8 (a : ℝ) (h : rf1852.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1852.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1852.rational a+Real.sqrt 2*evalQPoly rf1852.irrational a)/evalQPoly rf1852.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1852,rf1668]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/119 : ℚ)*Polynomial.X^0 + Polynomial.C (-18/119 : ℚ)*Polynomial.X^1 + Polynomial.C (118/119 : ℚ)*Polynomial.X^2 + Polynomial.C (-354/119 : ℚ)*Polynomial.X^3 + Polynomial.C (366/119 : ℚ)*Polynomial.X^4 + Polynomial.C (698/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-2522/119 : ℚ)*Polynomial.X^6 + Polynomial.C (2858/119 : ℚ)*Polynomial.X^7 + Polynomial.C (-75/7 : ℚ)*Polynomial.X^8
theorem eval9 (a : ℝ) (h : rf1898.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1898.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1898.rational a+Real.sqrt 2*evalQPoly rf1898.irrational a)/evalQPoly rf1898.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1898,rf1668]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/476 : ℚ)*Polynomial.X^0 + Polynomial.C (1/28 : ℚ)*Polynomial.X^1 + Polynomial.C (-24/119 : ℚ)*Polynomial.X^2 + Polynomial.C (44/119 : ℚ)*Polynomial.X^3 + Polynomial.C (115/238 : ℚ)*Polynomial.X^4 + Polynomial.C (-467/238 : ℚ)*Polynomial.X^5 + Polynomial.C (-22/17 : ℚ)*Polynomial.X^6 + Polynomial.C (542/119 : ℚ)*Polynomial.X^7 + Polynomial.C (3683/476 : ℚ)*Polynomial.X^8 + Polynomial.C (-661/68 : ℚ)*Polynomial.X^9
theorem eval10 (a : ℝ) (h : rf1874.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1874.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1874.rational a+Real.sqrt 2*evalQPoly rf1874.irrational a)/evalQPoly rf1874.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1874,rf1668]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-2/119 : ℚ)*Polynomial.X^4 + Polynomial.C (40/119 : ℚ)*Polynomial.X^5 + Polynomial.C (-156/119 : ℚ)*Polynomial.X^6 + Polynomial.C (-8/17 : ℚ)*Polynomial.X^7 + Polynomial.C (98/17 : ℚ)*Polynomial.X^8
theorem eval11 (a : ℝ) (h : rf1921.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1921.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1921.rational a+Real.sqrt 2*evalQPoly rf1921.irrational a)/evalQPoly rf1921.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1921,rf1668]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even076
