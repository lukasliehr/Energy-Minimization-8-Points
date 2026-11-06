import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even050
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1321.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-2/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (1/3910 : ℚ)*Polynomial.X^3 + Polynomial.C (13/1564 : ℚ)*Polynomial.X^4 + Polynomial.C (-7611/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (107/460 : ℚ)*Polynomial.X^6 + Polynomial.C (-3952/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1767/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (280603/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-134739/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (18645/5474 : ℚ)*Polynomial.X^11 + Polynomial.C (167947/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-446881/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (-73023/54740 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1321.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1321.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1321.rational a+Real.sqrt 2*evalQPoly rf1321.irrational a)/evalQPoly rf1321.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1321,rf1321]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (1/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (22/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (1/805 : ℚ)*Polynomial.X^6 + Polynomial.C (-2528/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (549/805 : ℚ)*Polynomial.X^8 + Polynomial.C (-7368/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-26737/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (58083/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-2746/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-202/85 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1340.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1340.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1340.rational a+Real.sqrt 2*evalQPoly rf1340.irrational a)/evalQPoly rf1340.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1340,rf1321]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (3/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-11/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-953/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (3329/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (-7947/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-2997/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (48681/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-148993/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (12471/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (91253/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-37/644 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1376.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1376.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1376.rational a+Real.sqrt 2*evalQPoly rf1376.irrational a)/evalQPoly rf1376.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1376,rf1321]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (1/1955 : ℚ)*Polynomial.X^4 + Polynomial.C (-19/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-61/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-52/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (2197/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-3469/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-6751/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (223/230 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1430.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1430.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1430.rational a+Real.sqrt 2*evalQPoly rf1430.irrational a)/evalQPoly rf1430.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1430,rf1321]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (1/6440 : ℚ)*Polynomial.X^1 + Polynomial.C (-11/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-433/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (8203/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-31053/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (6948/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-233/1190 : ℚ)*Polynomial.X^7 + Polynomial.C (-3785/3128 : ℚ)*Polynomial.X^8 + Polynomial.C (440119/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-41865/5474 : ℚ)*Polynomial.X^10 + Polynomial.C (18457/2380 : ℚ)*Polynomial.X^11 + Polynomial.C (-5369/15640 : ℚ)*Polynomial.X^12 + Polynomial.C (-546139/109480 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1357.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1357.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1357.rational a+Real.sqrt 2*evalQPoly rf1357.irrational a)/evalQPoly rf1357.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1357,rf1321]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (-3/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (25/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-144/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-412/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (14968/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-22993/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-2988/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (1737/230 : ℚ)*Polynomial.X^11 + Polynomial.C (-13139/1955 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1394.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1394.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1394.rational a+Real.sqrt 2*evalQPoly rf1394.irrational a)/evalQPoly rf1394.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1394,rf1321]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (27/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (228/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-3677/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (7/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-9967/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-13569/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (24383/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (-47347/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (10853/7820 : ℚ)*Polynomial.X^10 + Polynomial.C (193/805 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1447.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1447.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1447.rational a+Real.sqrt 2*evalQPoly rf1447.irrational a)/evalQPoly rf1447.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1447,rf1321]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-22/2737 : ℚ)*Polynomial.X^3 + Polynomial.C (7421/109480 : ℚ)*Polynomial.X^4 + Polynomial.C (-3012/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (173/782 : ℚ)*Polynomial.X^6 + Polynomial.C (5856/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-1227/1288 : ℚ)*Polynomial.X^8 + Polynomial.C (-4678/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (63569/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (222/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (58699/109480 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1411.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1411.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1411.rational a+Real.sqrt 2*evalQPoly rf1411.irrational a)/evalQPoly rf1411.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1411,rf1321]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (5/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-18/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-457/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (701/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (-4889/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-102/161 : ℚ)*Polynomial.X^9 + Polynomial.C (3023/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-1561/3910 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1465.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1465.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1465.rational a+Real.sqrt 2*evalQPoly rf1465.irrational a)/evalQPoly rf1465.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1465,rf1321]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/54740 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/3910 : ℚ)*Polynomial.X^1 + Polynomial.C (3/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (31/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-123/1190 : ℚ)*Polynomial.X^4 + Polynomial.C (702/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-2383/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-11337/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (9599/7820 : ℚ)*Polynomial.X^8 + Polynomial.C (19451/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (-1201/644 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1501.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1501.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1501.rational a+Real.sqrt 2*evalQPoly rf1501.irrational a)/evalQPoly rf1501.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1501,rf1321]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-4/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (19/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (248/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-3407/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (3396/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (5879/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-14464/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (2441/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (3208/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (13017/7820 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1482.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1482.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1482.rational a+Real.sqrt 2*evalQPoly rf1482.irrational a)/evalQPoly rf1482.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1482,rf1321]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (4/119 : ℚ)*Polynomial.X^4 + Polynomial.C (-492/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (163/595 : ℚ)*Polynomial.X^6 + Polynomial.C (6059/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-21956/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (3235/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (4661/3910 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1519.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1519.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1519.rational a+Real.sqrt 2*evalQPoly rf1519.irrational a)/evalQPoly rf1519.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1519,rf1321]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even050
