import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even042
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := Polynomial.X*rf1313.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (9/218960 : ℚ)*Polynomial.X^2 + Polynomial.C (-2/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (1891/218960 : ℚ)*Polynomial.X^4 + Polynomial.C (-151/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-1045/1904 : ℚ)*Polynomial.X^6 + Polynomial.C (69773/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-5546141/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (8861061/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-38523053/218960 : ℚ)*Polynomial.X^10 + Polynomial.C (731575/2737 : ℚ)*Polynomial.X^11 + Polynomial.C (-64403839/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (3921493/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (-7399113/43792 : ℚ)*Polynomial.X^14 + Polynomial.C (866786/13685 : ℚ)*Polynomial.X^15 + Polynomial.C (4415161/218960 : ℚ)*Polynomial.X^16 + Polynomial.C (-410583/15640 : ℚ)*Polynomial.X^17
theorem eval0 (a : ℝ) (h : rf1313.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1313.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1313.rational a+Real.sqrt 2*evalQPoly rf1313.irrational a)/evalQPoly rf1313.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1313,rf1313]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/437920 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-29/437920 : ℚ)*Polynomial.X^3 + Polynomial.C (29/9520 : ℚ)*Polynomial.X^4 + Polynomial.C (-10463/437920 : ℚ)*Polynomial.X^5 + Polynomial.C (2557/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-79069/437920 : ℚ)*Polynomial.X^7 + Polynomial.C (-219/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (380907/437920 : ℚ)*Polynomial.X^9 + Polynomial.C (-41043/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (380609/437920 : ℚ)*Polynomial.X^11 + Polynomial.C (569717/218960 : ℚ)*Polynomial.X^12 + Polynomial.C (-1670861/437920 : ℚ)*Polynomial.X^13 + Polynomial.C (-9777/54740 : ℚ)*Polynomial.X^14 + Polynomial.C (2307/736 : ℚ)*Polynomial.X^15 + Polynomial.C (-2037/1360 : ℚ)*Polynomial.X^16
theorem eval1 (a : ℝ) (h : rf1332.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1332.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1332.rational a+Real.sqrt 2*evalQPoly rf1332.irrational a)/evalQPoly rf1332.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1332,rf1313]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (83/109480 : ℚ)*Polynomial.X^3 + Polynomial.C (-79/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (24/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (44479/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-463441/109480 : ℚ)*Polynomial.X^7 + Polynomial.C (616937/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (-1037478/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (2635589/15640 : ℚ)*Polynomial.X^10 + Polynomial.C (-26669607/109480 : ℚ)*Polynomial.X^11 + Polynomial.C (2291925/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-202938/2737 : ℚ)*Polynomial.X^13 + Polynomial.C (-579763/21896 : ℚ)*Polynomial.X^14 + Polynomial.C (4647/184 : ℚ)*Polynomial.X^15
theorem eval2 (a : ℝ) (h : rf1368.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1368.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1368.rational a+Real.sqrt 2*evalQPoly rf1368.irrational a)/evalQPoly rf1368.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1368,rf1313]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-6/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (249/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-21/782 : ℚ)*Polynomial.X^6 + Polynomial.C (521/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (-2748/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (6217/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (265/2737 : ℚ)*Polynomial.X^10 + Polynomial.C (-66971/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (37206/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-175/68 : ℚ)*Polynomial.X^13 + Polynomial.C (203/230 : ℚ)*Polynomial.X^14
theorem eval3 (a : ℝ) (h : rf1422.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1422.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1422.rational a+Real.sqrt 2*evalQPoly rf1422.irrational a)/evalQPoly rf1422.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1422,rf1313]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-11/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (129/109480 : ℚ)*Polynomial.X^2 + Polynomial.C (-117/12880 : ℚ)*Polynomial.X^3 + Polynomial.C (-61/10948 : ℚ)*Polynomial.X^4 + Polynomial.C (133729/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-24919/4760 : ℚ)*Polynomial.X^6 + Polynomial.C (5402839/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (-292643/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (32698303/218960 : ℚ)*Polynomial.X^9 + Polynomial.C (-3977581/21896 : ℚ)*Polynomial.X^10 + Polynomial.C (525227/6256 : ℚ)*Polynomial.X^11 + Polynomial.C (1186699/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-8870929/43792 : ℚ)*Polynomial.X^13 + Polynomial.C (1601671/15640 : ℚ)*Polynomial.X^14 + Polynomial.C (1121321/43792 : ℚ)*Polynomial.X^15 + Polynomial.C (-66969/1955 : ℚ)*Polynomial.X^16
theorem eval4 (a : ℝ) (h : rf1349.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1349.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1349.rational a+Real.sqrt 2*evalQPoly rf1349.irrational a)/evalQPoly rf1349.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1349,rf1313]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (-1/437920 : ℚ)*Polynomial.X^0 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (1/437920 : ℚ)*Polynomial.X^2 + Polynomial.C (-53/31280 : ℚ)*Polynomial.X^3 + Polynomial.C (5511/437920 : ℚ)*Polynomial.X^4 + Polynomial.C (-129/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (44777/437920 : ℚ)*Polynomial.X^6 + Polynomial.C (-12757/218960 : ℚ)*Polynomial.X^7 + Polynomial.C (-252667/437920 : ℚ)*Polynomial.X^8 + Polynomial.C (289047/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-2283973/437920 : ℚ)*Polynomial.X^10 + Polynomial.C (507027/218960 : ℚ)*Polynomial.X^11 + Polynomial.C (222867/19040 : ℚ)*Polynomial.X^12 + Polynomial.C (-206631/7820 : ℚ)*Polynomial.X^13 + Polynomial.C (16665/736 : ℚ)*Polynomial.X^14 + Polynomial.C (-221949/31280 : ℚ)*Polynomial.X^15
theorem eval5 (a : ℝ) (h : rf1386.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1386.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1386.rational a+Real.sqrt 2*evalQPoly rf1386.irrational a)/evalQPoly rf1386.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1386,rf1313]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-12/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (377/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (83/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-24721/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (53523/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-505663/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (109059/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (-1515854/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (112836/805 : ℚ)*Polynomial.X^10 + Polynomial.C (-5475899/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (588747/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (201883/10948 : ℚ)*Polynomial.X^13 + Polynomial.C (-1161/115 : ℚ)*Polynomial.X^14
theorem eval6 (a : ℝ) (h : rf1439.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1439.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1439.rational a+Real.sqrt 2*evalQPoly rf1439.irrational a)/evalQPoly rf1439.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1439,rf1313]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-7/15640 : ℚ)*Polynomial.X^2 + Polynomial.C (41/10948 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^4 + Polynomial.C (-3088/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (236127/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (-2603/230 : ℚ)*Polynomial.X^7 + Polynomial.C (109630/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (-800249/7820 : ℚ)*Polynomial.X^9 + Polynomial.C (20977997/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (-13929551/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (5885359/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-2158097/27370 : ℚ)*Polynomial.X^13 + Polynomial.C (-3240283/109480 : ℚ)*Polynomial.X^14 + Polynomial.C (61629/1955 : ℚ)*Polynomial.X^15
theorem eval7 (a : ℝ) (h : rf1403.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1403.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1403.rational a+Real.sqrt 2*evalQPoly rf1403.irrational a)/evalQPoly rf1403.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1403,rf1313]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/218960 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^2 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (79/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (-739/218960 : ℚ)*Polynomial.X^5 + Polynomial.C (-1181/109480 : ℚ)*Polynomial.X^6 + Polynomial.C (471/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (545/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-13171/31280 : ℚ)*Polynomial.X^9 + Polynomial.C (5393/109480 : ℚ)*Polynomial.X^10 + Polynomial.C (67621/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-12477/10948 : ℚ)*Polynomial.X^12 + Polynomial.C (-69/272 : ℚ)*Polynomial.X^13 + Polynomial.C (6391/15640 : ℚ)*Polynomial.X^14
theorem eval8 (a : ℝ) (h : rf1457.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1457.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1457.rational a+Real.sqrt 2*evalQPoly rf1457.irrational a)/evalQPoly rf1457.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1457,rf1313]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (53/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-27/3220 : ℚ)*Polynomial.X^3 + Polynomial.C (-39/54740 : ℚ)*Polynomial.X^4 + Polynomial.C (30159/54740 : ℚ)*Polynomial.X^5 + Polynomial.C (-130381/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (583659/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (-1596461/27370 : ℚ)*Polynomial.X^8 + Polynomial.C (272684/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (-5442219/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (461857/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (712849/54740 : ℚ)*Polynomial.X^12 + Polynomial.C (-1471/92 : ℚ)*Polynomial.X^13
theorem eval9 (a : ℝ) (h : rf1493.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1493.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1493.rational a+Real.sqrt 2*evalQPoly rf1493.irrational a)/evalQPoly rf1493.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1493,rf1313]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^2 + Polynomial.C (53/7820 : ℚ)*Polynomial.X^3 + Polynomial.C (541/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-77771/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (113423/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-68147/5474 : ℚ)*Polynomial.X^7 + Polynomial.C (9806/595 : ℚ)*Polynomial.X^8 + Polynomial.C (1358353/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-2273213/27370 : ℚ)*Polynomial.X^10 + Polynomial.C (6957611/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (-200611/2737 : ℚ)*Polynomial.X^12 + Polynomial.C (-1364877/109480 : ℚ)*Polynomial.X^13 + Polynomial.C (99271/3910 : ℚ)*Polynomial.X^14
theorem eval10 (a : ℝ) (h : rf1474.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1474.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1474.rational a+Real.sqrt 2*evalQPoly rf1474.irrational a)/evalQPoly rf1474.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1474,rf1313]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (1/218960 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/21896 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (181/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-779/43792 : ℚ)*Polynomial.X^4 + Polynomial.C (37/920 : ℚ)*Polynomial.X^5 + Polynomial.C (-9/782 : ℚ)*Polynomial.X^6 + Polynomial.C (-277/1610 : ℚ)*Polynomial.X^7 + Polynomial.C (120179/218960 : ℚ)*Polynomial.X^8 + Polynomial.C (-91087/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-849/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (26793/10948 : ℚ)*Polynomial.X^11 + Polynomial.C (-100251/31280 : ℚ)*Polynomial.X^12 + Polynomial.C (19719/15640 : ℚ)*Polynomial.X^13
theorem eval11 (a : ℝ) (h : rf1511.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1511.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1511.rational a+Real.sqrt 2*evalQPoly rf1511.irrational a)/evalQPoly rf1511.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1511,rf1313]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even042
