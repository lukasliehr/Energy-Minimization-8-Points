import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even032
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1063.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (9/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (208/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-7627/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (14397/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-2721/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (2321/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (2823/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-19714/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (44664/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-35741/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-141/340 : ℚ)*Polynomial.X^13 + Polynomial.C (1161/3910 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1063.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1063.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1063.rational a+Real.sqrt 2*evalQPoly rf1063.irrational a)/evalQPoly rf1063.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1063,rf1063]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (53/3910 : ℚ)*Polynomial.X^4 + Polynomial.C (-186/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (1202/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (331/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (-26143/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (2961/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (20231/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (-28386/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-5506/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (76/85 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1078.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1078.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1078.rational a+Real.sqrt 2*evalQPoly rf1078.irrational a)/evalQPoly rf1078.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1078,rf1063]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/3220 : ℚ)*Polynomial.X^2 + Polynomial.C (-43/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-887/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (831/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-2173/3910 : ℚ)*Polynomial.X^6 + Polynomial.C (23869/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1271/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-77477/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (55781/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (2349/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (7/92 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1106.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1106.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1106.rational a+Real.sqrt 2*evalQPoly rf1106.irrational a)/evalQPoly rf1106.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1106,rf1063]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (8/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-26/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-24/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (1209/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1864/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-2306/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (7848/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (-79/230 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1148.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1148.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1148.rational a+Real.sqrt 2*evalQPoly rf1148.irrational a)/evalQPoly rf1148.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1148,rf1063]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-37/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-821/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (1903/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-28909/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (5317/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-3123/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-52477/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (61541/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-153997/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (228867/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-124767/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (10213/7820 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1091.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1091.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1091.rational a+Real.sqrt 2*evalQPoly rf1091.irrational a)/evalQPoly rf1091.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1091,rf1063]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (11/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-75/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (30/391 : ℚ)*Polynomial.X^4 + Polynomial.C (-2097/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-3329/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (4423/3910 : ℚ)*Polynomial.X^7 + Polynomial.C (-20143/10948 : ℚ)*Polynomial.X^8 + Polynomial.C (-369/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (108457/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (-10063/1955 : ℚ)*Polynomial.X^11 + Polynomial.C (4207/1955 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1120.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1120.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1120.rational a+Real.sqrt 2*evalQPoly rf1120.irrational a)/evalQPoly rf1120.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1120,rf1063]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (41/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (181/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-815/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (2803/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (-19199/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-145/782 : ℚ)*Polynomial.X^7 + Polynomial.C (85717/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-90749/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (48597/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-133/460 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1161.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1161.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1161.rational a+Real.sqrt 2*evalQPoly rf1161.irrational a)/evalQPoly rf1161.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1161,rf1063]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (327/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-2518/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (1346/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-17628/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (17489/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-457/322 : ℚ)*Polynomial.X^10 + Polynomial.C (44349/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (-469/3910 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1133.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1133.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1133.rational a+Real.sqrt 2*evalQPoly rf1133.irrational a)/evalQPoly rf1133.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1133,rf1063]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (727/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-413/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (1697/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (907/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (-32563/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-2697/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (54/23 : ℚ)*Polynomial.X^10 + Polynomial.C (-5887/3910 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1175.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1175.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1175.rational a+Real.sqrt 2*evalQPoly rf1175.irrational a)/evalQPoly rf1175.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1175,rf1063]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-16/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (394/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-1639/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (2687/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-4292/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (762/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-32523/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (7/46 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1203.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1203.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1203.rational a+Real.sqrt 2*evalQPoly rf1203.irrational a)/evalQPoly rf1203.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1203,rf1063]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-13/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (813/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-537/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (7073/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-6561/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-4329/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (49449/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-28433/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (184593/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-6701/7820 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1188.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1188.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1188.rational a+Real.sqrt 2*evalQPoly rf1188.irrational a)/evalQPoly rf1188.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1188,rf1063]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^2 + Polynomial.C (97/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (-547/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (541/5474 : ℚ)*Polynomial.X^5 + Polynomial.C (71/238 : ℚ)*Polynomial.X^6 + Polynomial.C (-21379/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (603/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (8586/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-929/1955 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1217.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1217.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1217.rational a+Real.sqrt 2*evalQPoly rf1217.irrational a)/evalQPoly rf1217.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1217,rf1063]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even032
