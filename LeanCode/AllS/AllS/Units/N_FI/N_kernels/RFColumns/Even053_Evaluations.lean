import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even053
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1324.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/68 : ℚ)*Polynomial.X^2 + Polynomial.C (8/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-145/68 : ℚ)*Polynomial.X^4 + Polynomial.C (185/34 : ℚ)*Polynomial.X^5 + Polynomial.C (-581/68 : ℚ)*Polynomial.X^6 + Polynomial.C (115/17 : ℚ)*Polynomial.X^7 + Polynomial.C (25/68 : ℚ)*Polynomial.X^8 + Polynomial.C (-79/34 : ℚ)*Polynomial.X^9
theorem eval0 (a : ℝ) (h : rf1324.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1324.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1324.rational a+Real.sqrt 2*evalQPoly rf1324.irrational a)/evalQPoly rf1324.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1324,rf1324]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/68 : ℚ)*Polynomial.X^1 + Polynomial.C (3/34 : ℚ)*Polynomial.X^2 + Polynomial.C (7/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-75/34 : ℚ)*Polynomial.X^4 + Polynomial.C (485/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-307/34 : ℚ)*Polynomial.X^6 + Polynomial.C (117/68 : ℚ)*Polynomial.X^7 + Polynomial.C (139/34 : ℚ)*Polynomial.X^8
theorem eval1 (a : ℝ) (h : rf1343.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1343.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1343.rational a+Real.sqrt 2*evalQPoly rf1343.irrational a)/evalQPoly rf1343.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1343,rf1324]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/68 : ℚ)*Polynomial.X^1 + Polynomial.C (4/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-89/68 : ℚ)*Polynomial.X^3 + Polynomial.C (56/17 : ℚ)*Polynomial.X^4 + Polynomial.C (-219/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-4/17 : ℚ)*Polynomial.X^6 + Polynomial.C (5/4 : ℚ)*Polynomial.X^7
theorem eval2 (a : ℝ) (h : rf1379.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1379.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1379.rational a+Real.sqrt 2*evalQPoly rf1379.irrational a)/evalQPoly rf1379.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1379,rf1324]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (0 : ℚ)*Polynomial.X^1 + Polynomial.C (0 : ℚ)*Polynomial.X^2 + Polynomial.C (0 : ℚ)*Polynomial.X^3 + Polynomial.C (-1/17 : ℚ)*Polynomial.X^4 + Polynomial.C (10/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-1 : ℚ)*Polynomial.X^6
theorem eval3 (a : ℝ) (h : rf1433.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1433.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1433.rational a+Real.sqrt 2*evalQPoly rf1433.irrational a)/evalQPoly rf1433.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1433,rf1324]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (1/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-47/68 : ℚ)*Polynomial.X^2 + Polynomial.C (117/34 : ℚ)*Polynomial.X^3 + Polynomial.C (-665/68 : ℚ)*Polynomial.X^4 + Polynomial.C (300/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-1425/68 : ℚ)*Polynomial.X^6 + Polynomial.C (33/2 : ℚ)*Polynomial.X^7 + Polynomial.C (-423/68 : ℚ)*Polynomial.X^8
theorem eval4 (a : ℝ) (h : rf1360.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1360.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1360.rational a+Real.sqrt 2*evalQPoly rf1360.irrational a)/evalQPoly rf1360.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1360,rf1324]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/68 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/4 : ℚ)*Polynomial.X^2 + Polynomial.C (197/68 : ℚ)*Polynomial.X^3 + Polynomial.C (-673/68 : ℚ)*Polynomial.X^4 + Polynomial.C (1237/68 : ℚ)*Polynomial.X^5 + Polynomial.C (-1327/68 : ℚ)*Polynomial.X^6 + Polynomial.C (715/68 : ℚ)*Polynomial.X^7
theorem eval5 (a : ℝ) (h : rf1397.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1397.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1397.rational a+Real.sqrt 2*evalQPoly rf1397.irrational a)/evalQPoly rf1397.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1397,rf1324]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (-9/34 : ℚ)*Polynomial.X^1 + Polynomial.C (7/4 : ℚ)*Polynomial.X^2 + Polynomial.C (-95/17 : ℚ)*Polynomial.X^3 + Polynomial.C (623/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-249/34 : ℚ)*Polynomial.X^5 + Polynomial.C (9/4 : ℚ)*Polynomial.X^6
theorem eval6 (a : ℝ) (h : rf1450.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1450.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1450.rational a+Real.sqrt 2*evalQPoly rf1450.irrational a)/evalQPoly rf1450.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1450,rf1324]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (4/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-99/68 : ℚ)*Polynomial.X^2 + Polynomial.C (167/34 : ℚ)*Polynomial.X^3 + Polynomial.C (-679/68 : ℚ)*Polynomial.X^4 + Polynomial.C (225/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-821/68 : ℚ)*Polynomial.X^6 + Polynomial.C (175/34 : ℚ)*Polynomial.X^7
theorem eval7 (a : ℝ) (h : rf1414.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1414.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1414.rational a+Real.sqrt 2*evalQPoly rf1414.irrational a)/evalQPoly rf1414.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1414,rf1324]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (3/17 : ℚ)*Polynomial.X^1 + Polynomial.C (-57/68 : ℚ)*Polynomial.X^2 + Polynomial.C (46/17 : ℚ)*Polynomial.X^3 + Polynomial.C (-27/4 : ℚ)*Polynomial.X^4 + Polynomial.C (183/17 : ℚ)*Polynomial.X^5 + Polynomial.C (-539/68 : ℚ)*Polynomial.X^6
theorem eval8 (a : ℝ) (h : rf1468.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1468.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1468.rational a+Real.sqrt 2*evalQPoly rf1468.irrational a)/evalQPoly rf1468.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1468,rf1324]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (-15/34 : ℚ)*Polynomial.X^1 + Polynomial.C (39/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-101/17 : ℚ)*Polynomial.X^3 + Polynomial.C (257/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-7/2 : ℚ)*Polynomial.X^5
theorem eval9 (a : ℝ) (h : rf1504.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1504.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1504.rational a+Real.sqrt 2*evalQPoly rf1504.irrational a)/evalQPoly rf1504.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1504,rf1324]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/68 : ℚ)*Polynomial.X^0 + Polynomial.C (5/34 : ℚ)*Polynomial.X^1 + Polynomial.C (-39/68 : ℚ)*Polynomial.X^2 + Polynomial.C (15/17 : ℚ)*Polynomial.X^3 + Polynomial.C (65/68 : ℚ)*Polynomial.X^4 + Polynomial.C (-163/34 : ℚ)*Polynomial.X^5 + Polynomial.C (231/68 : ℚ)*Polynomial.X^6
theorem eval10 (a : ℝ) (h : rf1485.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1485.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1485.rational a+Real.sqrt 2*evalQPoly rf1485.irrational a)/evalQPoly rf1485.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1485,rf1324]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (-1/34 : ℚ)*Polynomial.X^0 + Polynomial.C (5/34 : ℚ)*Polynomial.X^1 + Polynomial.C (1/17 : ℚ)*Polynomial.X^2 + Polynomial.C (-41/17 : ℚ)*Polynomial.X^3 + Polynomial.C (239/34 : ℚ)*Polynomial.X^4 + Polynomial.C (-227/34 : ℚ)*Polynomial.X^5
theorem eval11 (a : ℝ) (h : rf1522.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1522.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1522.rational a+Real.sqrt 2*evalQPoly rf1522.irrational a)/evalQPoly rf1522.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1522,rf1324]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even053
