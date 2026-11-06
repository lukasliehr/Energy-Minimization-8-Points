import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even061
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1653.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (19/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1549/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (1301/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-656/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-175379/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (2828051/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-6595359/54740 : ℚ)*Polynomial.X^7 + Polynomial.C (5215683/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-10913142/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (105910793/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-240183/782 : ℚ)*Polynomial.X^11 + Polynomial.C (-12106427/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (807073/644 : ℚ)*Polynomial.X^13 + Polynomial.C (-487059/1288 : ℚ)*Polynomial.X^14 + Polynomial.C (-15141083/54740 : ℚ)*Polynomial.X^15
theorem eval0 (a : ℝ) (h : rf1653.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1653.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1653.rational a+Real.sqrt 2*evalQPoly rf1653.irrational a)/evalQPoly rf1653.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1653,rf1653]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (4/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-16/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (25/644 : ℚ)*Polynomial.X^2 + Polynomial.C (-1079/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-70543/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (541307/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-79144/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (2689989/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-122721/1190 : ℚ)*Polynomial.X^8 + Polynomial.C (-4177389/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (39163149/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-1624161/1564 : ℚ)*Polynomial.X^11 + Polynomial.C (29097533/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (15385743/54740 : ℚ)*Polynomial.X^13 + Polynomial.C (-66309/170 : ℚ)*Polynomial.X^14
theorem eval1 (a : ℝ) (h : rf1677.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1677.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1677.rational a+Real.sqrt 2*evalQPoly rf1677.irrational a)/evalQPoly rf1677.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1677,rf1653]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-393/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (401/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-589/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-1167/782 : ℚ)*Polynomial.X^4 + Polynomial.C (274945/21896 : ℚ)*Polynomial.X^5 + Polynomial.C (-154680/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (4547737/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-4419249/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (40818817/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-2215037/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-8119173/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (5757427/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-58825/1288 : ℚ)*Polynomial.X^13
theorem eval2 (a : ℝ) (h : rf1723.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1723.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1723.rational a+Real.sqrt 2*evalQPoly rf1723.irrational a)/evalQPoly rf1723.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1723,rf1653]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (-2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (1/595 : ℚ)*Polynomial.X^1 + Polynomial.C (12/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-673/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-228/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (7270/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-1488/119 : ℚ)*Polynomial.X^6 + Polynomial.C (425862/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-453826/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-648693/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (2829972/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-770305/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (18864/115 : ℚ)*Polynomial.X^12
theorem eval3 (a : ℝ) (h : rf1792.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1792.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1792.rational a+Real.sqrt 2*evalQPoly rf1792.irrational a)/evalQPoly rf1792.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1792,rf1653]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-3/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (25/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (-267/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (1019/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (479/805 : ℚ)*Polynomial.X^4 + Polynomial.C (-149761/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (3214159/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-3280413/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (10455127/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-48221543/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (142845153/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-10056413/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-5795369/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (19722079/13685 : ℚ)*Polynomial.X^13 + Polynomial.C (-108947299/109480 : ℚ)*Polynomial.X^14
theorem eval4 (a : ℝ) (h : rf1699.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1699.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1699.rational a+Real.sqrt 2*evalQPoly rf1699.irrational a)/evalQPoly rf1699.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1699,rf1653]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (2/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (-277/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1361/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-591/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (-5621/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (790093/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-937303/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (2684331/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-4149893/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-175739/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (186653/170 : ℚ)*Polynomial.X^10 + Polynomial.C (-65231659/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (412473/170 : ℚ)*Polynomial.X^12 + Polynomial.C (-8561371/7820 : ℚ)*Polynomial.X^13
theorem eval5 (a : ℝ) (h : rf1746.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1746.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1746.rational a+Real.sqrt 2*evalQPoly rf1746.irrational a)/evalQPoly rf1746.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1746,rf1653]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (5/21896 : ℚ)*Polynomial.X^0 + Polynomial.C (-233/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (381/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (10929/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-229331/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (55911/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-109810/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (44685/322 : ℚ)*Polynomial.X^7 + Polynomial.C (-38420253/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (31467123/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-15517401/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (886093/3220 : ℚ)*Polynomial.X^11 + Polynomial.C (-120921/6440 : ℚ)*Polynomial.X^12
theorem eval6 (a : ℝ) (h : rf1814.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1814.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1814.rational a+Real.sqrt 2*evalQPoly rf1814.irrational a)/evalQPoly rf1814.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1814,rf1653]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-13/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (31/1610 : ℚ)*Polynomial.X^2 + Polynomial.C (-15789/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (147463/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-14407/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-232266/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (568007/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-2194399/6440 : ℚ)*Polynomial.X^8 + Polynomial.C (5631309/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (-800681/782 : ℚ)*Polynomial.X^10 + Polynomial.C (10838379/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-9440829/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (6033231/27370 : ℚ)*Polynomial.X^13
theorem eval7 (a : ℝ) (h : rf1768.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1768.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1768.rational a+Real.sqrt 2*evalQPoly rf1768.irrational a)/evalQPoly rf1768.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1768,rf1653]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-6/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (453/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-465/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-1261/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (126169/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-346639/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (1063807/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-1626921/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-495051/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (13459881/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-673779/1564 : ℚ)*Polynomial.X^10 + Polynomial.C (2600069/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-535437/7820 : ℚ)*Polynomial.X^12
theorem eval8 (a : ℝ) (h : rf1837.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1837.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1837.rational a+Real.sqrt 2*evalQPoly rf1837.irrational a)/evalQPoly rf1837.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1837,rf1653]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (-3/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (131/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-2391/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (3491/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-4667/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-277013/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (338001/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-5029741/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (18383353/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-21556121/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (2146987/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (-57537/644 : ℚ)*Polynomial.X^11
theorem eval9 (a : ℝ) (h : rf1883.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1883.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1883.rational a+Real.sqrt 2*evalQPoly rf1883.irrational a)/evalQPoly rf1883.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1883,rf1653]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/10948 : ℚ)*Polynomial.X^1 + Polynomial.C (53/2737 : ℚ)*Polynomial.X^2 + Polynomial.C (-10011/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (7073/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (8637/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (-245711/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (88317/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (-8725187/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-326057/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (926182/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-361395/644 : ℚ)*Polynomial.X^11 + Polynomial.C (6059579/15640 : ℚ)*Polynomial.X^12
theorem eval10 (a : ℝ) (h : rf1859.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1859.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1859.rational a+Real.sqrt 2*evalQPoly rf1859.irrational a)/evalQPoly rf1859.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1859,rf1653]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-4/13685 : ℚ)*Polynomial.X^0 + Polynomial.C (213/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-29/595 : ℚ)*Polynomial.X^2 + Polynomial.C (-2899/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (34812/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-189107/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (111886/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-46967/805 : ℚ)*Polynomial.X^7 + Polynomial.C (-466944/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (1501181/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-5816739/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (1070071/3910 : ℚ)*Polynomial.X^11
theorem eval11 (a : ℝ) (h : rf1906.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1906.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1906.rational a+Real.sqrt 2*evalQPoly rf1906.irrational a)/evalQPoly rf1906.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1906,rf1653]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even061
