import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even063
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1655.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (79/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (157/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-12991/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (42355/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (-24800/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (384397/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-3303553/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (10043241/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-159503/1610 : ℚ)*Polynomial.X^11 + Polynomial.C (56347/782 : ℚ)*Polynomial.X^12 + Polynomial.C (-1398849/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-747419/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (131352/13685 : ℚ)*Polynomial.X^15 + Polynomial.C (-8048/1955 : ℚ)*Polynomial.X^16
theorem eval0 (a : ℝ) (h : rf1655.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1655.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1655.rational a+Real.sqrt 2*evalQPoly rf1655.irrational a)/evalQPoly rf1655.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1655,rf1655]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/43792 : ℚ)*Polynomial.X^2 + Polynomial.C (89/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/280 : ℚ)*Polynomial.X^4 + Polynomial.C (-699/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (33/31280 : ℚ)*Polynomial.X^6 + Polynomial.C (20613/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (-8511/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (229413/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (2851/2576 : ℚ)*Polynomial.X^10 + Polynomial.C (-23641/3910 : ℚ)*Polynomial.X^11 + Polynomial.C (884733/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-25545/43792 : ℚ)*Polynomial.X^13 + Polynomial.C (-1908047/218960 : ℚ)*Polynomial.X^14 + Polynomial.C (3877/680 : ℚ)*Polynomial.X^15
theorem eval1 (a : ℝ) (h : rf1679.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1679.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1679.rational a+Real.sqrt 2*evalQPoly rf1679.irrational a)/evalQPoly rf1679.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1679,rf1655]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (43/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-137/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-79/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (6023/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-191599/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (228387/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-726333/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (3104147/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-1223253/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (3380099/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-177263/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-166776/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (1613/184 : ℚ)*Polynomial.X^14
theorem eval2 (a : ℝ) (h : rf1725.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1725.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1725.rational a+Real.sqrt 2*evalQPoly rf1725.irrational a)/evalQPoly rf1725.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1725,rf1655]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (9/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-47/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-57/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (3481/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-999/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (16431/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-29369/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (31281/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (1503/476 : ℚ)*Polynomial.X^10 + Polynomial.C (-420751/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (65261/7820 : ℚ)*Polynomial.X^12 + Polynomial.C (-3199/920 : ℚ)*Polynomial.X^13
theorem eval3 (a : ℝ) (h : rf1794.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1794.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1794.rational a+Real.sqrt 2*evalQPoly rf1794.irrational a)/evalQPoly rf1794.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1794,rf1655]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (9/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (-321/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-93/21896 : ℚ)*Polynomial.X^3 + Polynomial.C (2936/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-189401/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (865377/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-16083/680 : ℚ)*Polynomial.X^7 + Polynomial.C (2600191/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-289027/4760 : ℚ)*Polynomial.X^9 + Polynomial.C (835813/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (1321737/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-239707/5474 : ℚ)*Polynomial.X^12 + Polynomial.C (816381/21896 : ℚ)*Polynomial.X^13 + Polynomial.C (-2019897/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (53229/15640 : ℚ)*Polynomial.X^15
theorem eval4 (a : ℝ) (h : rf1701.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1701.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1701.rational a+Real.sqrt 2*evalQPoly rf1701.irrational a)/evalQPoly rf1701.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1701,rf1655]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (11/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-31/15640 : ℚ)*Polynomial.X^3 + Polynomial.C (449/43792 : ℚ)*Polynomial.X^4 + Polynomial.C (-159/43792 : ℚ)*Polynomial.X^5 + Polynomial.C (-4365/21896 : ℚ)*Polynomial.X^6 + Polynomial.C (66327/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (-831743/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (1348573/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (-1807/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (-2279253/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (575691/12880 : ℚ)*Polynomial.X^12 + Polynomial.C (-9518797/218960 : ℚ)*Polynomial.X^13 + Polynomial.C (258809/15640 : ℚ)*Polynomial.X^14
theorem eval5 (a : ℝ) (h : rf1748.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1748.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1748.rational a+Real.sqrt 2*evalQPoly rf1748.irrational a)/evalQPoly rf1748.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1748,rf1655]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (6/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (99/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1407/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (4053/3128 : ℚ)*Polynomial.X^5 + Polynomial.C (-78654/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (239583/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-2008961/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (5551253/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-565508/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (169886/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (393097/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-4749/920 : ℚ)*Polynomial.X^13
theorem eval6 (a : ℝ) (h : rf1816.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1816.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1816.rational a+Real.sqrt 2*evalQPoly rf1816.irrational a)/evalQPoly rf1816.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1816,rf1655]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (3/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-929/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (60603/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-185469/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (34900/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-460106/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (7130169/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-1000775/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (1163383/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-1120251/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-3551/6440 : ℚ)*Polynomial.X^13 + Polynomial.C (64843/7820 : ℚ)*Polynomial.X^14
theorem eval7 (a : ℝ) (h : rf1770.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1770.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1770.rational a+Real.sqrt 2*evalQPoly rf1770.irrational a)/evalQPoly rf1770.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1770,rf1655]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (13/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/4760 : ℚ)*Polynomial.X^3 + Polynomial.C (281/21896 : ℚ)*Polynomial.X^4 + Polynomial.C (-1215/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (10063/54740 : ℚ)*Polynomial.X^6 + Polynomial.C (-1389/3220 : ℚ)*Polynomial.X^7 + Polynomial.C (28683/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (20259/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-337531/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (628121/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-62053/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (11123/15640 : ℚ)*Polynomial.X^13
theorem eval8 (a : ℝ) (h : rf1839.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1839.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1839.rational a+Real.sqrt 2*evalQPoly rf1839.irrational a)/evalQPoly rf1839.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1839,rf1655]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/7820 : ℚ)*Polynomial.X^1 + Polynomial.C (-131/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (501/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (5903/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-7365/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (36909/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-528351/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (931319/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-399457/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (1137201/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-106919/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-319/92 : ℚ)*Polynomial.X^12
theorem eval9 (a : ℝ) (h : rf1885.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1885.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1885.rational a+Real.sqrt 2*evalQPoly rf1885.irrational a)/evalQPoly rf1885.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1885,rf1655]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-41/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/476 : ℚ)*Polynomial.X^2 + Polynomial.C (123/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-5989/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (144309/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-110591/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (30087/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (183849/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-2751687/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (2183627/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-44831/1564 : ℚ)*Polynomial.X^11 + Polynomial.C (13224/1955 : ℚ)*Polynomial.X^12 + Polynomial.C (47117/15640 : ℚ)*Polynomial.X^13
theorem eval10 (a : ℝ) (h : rf1861.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1861.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1861.rational a+Real.sqrt 2*evalQPoly rf1861.irrational a)/evalQPoly rf1861.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1861,rf1655]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (507/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-236/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-89/7820 : ℚ)*Polynomial.X^5 + Polynomial.C (2151/7820 : ℚ)*Polynomial.X^6 + Polynomial.C (-47367/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (107837/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (86967/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-99929/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (767043/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (-28209/7820 : ℚ)*Polynomial.X^12
theorem eval11 (a : ℝ) (h : rf1908.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1908.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1908.rational a+Real.sqrt 2*evalQPoly rf1908.irrational a)/evalQPoly rf1908.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1908,rf1655]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even063
