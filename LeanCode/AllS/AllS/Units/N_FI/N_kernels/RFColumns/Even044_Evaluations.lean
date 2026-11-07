import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even044
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def den : Polynomial ℚ := rf1315.denominator
def n0 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/109480 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-163/27370 : ℚ)*Polynomial.X^3 + Polynomial.C (891/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (-21101/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (-1541/2380 : ℚ)*Polynomial.X^6 + Polynomial.C (96062/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-363038/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (6122441/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-3150067/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-301377/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (1172327/13685 : ℚ)*Polynomial.X^12 + Polynomial.C (-715913/15640 : ℚ)*Polynomial.X^13 + Polynomial.C (-187891/7820 : ℚ)*Polynomial.X^14
theorem eval0 (a : ℝ) (h : rf1315.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1315.eval a=evalQPoly n0 a/evalQPoly den a := by
  change (evalQPoly rf1315.rational a+Real.sqrt 2*evalQPoly rf1315.irrational a)/evalQPoly rf1315.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n0,den,rf1315,rf1315]
  all_goals ring
#print axioms eval0

def n1 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (2/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (-79/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (7/391 : ℚ)*Polynomial.X^3 + Polynomial.C (79/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-1565/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (2531/805 : ℚ)*Polynomial.X^6 + Polynomial.C (-106732/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (11819/1955 : ℚ)*Polynomial.X^8 + Polynomial.C (242146/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-89639/1610 : ℚ)*Polynomial.X^10 + Polynomial.C (773711/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (39447/27370 : ℚ)*Polynomial.X^12 + Polynomial.C (-2763/85 : ℚ)*Polynomial.X^13
theorem eval1 (a : ℝ) (h : rf1334.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1334.eval a=evalQPoly n1 a/evalQPoly den a := by
  change (evalQPoly rf1334.rational a+Real.sqrt 2*evalQPoly rf1334.irrational a)/evalQPoly rf1334.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n1,den,rf1334,rf1315]
  all_goals ring
#print axioms eval1

def n2 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/7820 : ℚ)*Polynomial.X^2 + Polynomial.C (607/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (-467/7820 : ℚ)*Polynomial.X^4 + Polynomial.C (-4909/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (79151/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-323297/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (128671/5474 : ℚ)*Polynomial.X^8 + Polynomial.C (-236129/10948 : ℚ)*Polynomial.X^9 + Polynomial.C (-43529/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (116869/7820 : ℚ)*Polynomial.X^11 + Polynomial.C (-363/92 : ℚ)*Polynomial.X^12
theorem eval2 (a : ℝ) (h : rf1370.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1370.eval a=evalQPoly n2 a/evalQPoly den a := by
  change (evalQPoly rf1370.rational a+Real.sqrt 2*evalQPoly rf1370.irrational a)/evalQPoly rf1370.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n2,den,rf1370,rf1315]
  all_goals ring
#print axioms eval2

def n3 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (13/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-3/1955 : ℚ)*Polynomial.X^3 + Polynomial.C (-12/805 : ℚ)*Polynomial.X^4 + Polynomial.C (-18/805 : ℚ)*Polynomial.X^5 + Polynomial.C (1726/2737 : ℚ)*Polynomial.X^6 + Polynomial.C (-330/161 : ℚ)*Polynomial.X^7 + Polynomial.C (27588/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (45139/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-180539/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (1521/115 : ℚ)*Polynomial.X^11
theorem eval3 (a : ℝ) (h : rf1424.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1424.eval a=evalQPoly n3 a/evalQPoly den a := by
  change (evalQPoly rf1424.rational a+Real.sqrt 2*evalQPoly rf1424.irrational a)/evalQPoly rf1424.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n3,den,rf1424,rf1315]
  all_goals ring
#print axioms eval3

def n4 : Polynomial ℚ := Polynomial.C (-3/109480 : ℚ)*Polynomial.X^0 + Polynomial.C (7/15640 : ℚ)*Polynomial.X^1 + Polynomial.C (-43/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (-159/5474 : ℚ)*Polynomial.X^3 + Polynomial.C (4101/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (-100091/109480 : ℚ)*Polynomial.X^5 + Polynomial.C (2991/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (100386/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (-3508429/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (7680011/109480 : ℚ)*Polynomial.X^9 + Polynomial.C (-950303/10948 : ℚ)*Polynomial.X^10 + Polynomial.C (817447/27370 : ℚ)*Polynomial.X^11 + Polynomial.C (8175757/109480 : ℚ)*Polynomial.X^12 + Polynomial.C (-1337143/15640 : ℚ)*Polynomial.X^13
theorem eval4 (a : ℝ) (h : rf1351.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1351.eval a=evalQPoly n4 a/evalQPoly den a := by
  change (evalQPoly rf1351.rational a+Real.sqrt 2*evalQPoly rf1351.irrational a)/evalQPoly rf1351.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n4,den,rf1351,rf1315]
  all_goals ring
#print axioms eval4

def n5 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (3/27370 : ℚ)*Polynomial.X^1 + Polynomial.C (-38/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (284/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-61/27370 : ℚ)*Polynomial.X^4 + Polynomial.C (-10721/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (3952/805 : ℚ)*Polynomial.X^6 + Polynomial.C (-198036/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (52359/2737 : ℚ)*Polynomial.X^8 + Polynomial.C (65851/5474 : ℚ)*Polynomial.X^9 + Polynomial.C (-1249182/13685 : ℚ)*Polynomial.X^10 + Polynomial.C (2014788/13685 : ℚ)*Polynomial.X^11 + Polynomial.C (-361047/3910 : ℚ)*Polynomial.X^12
theorem eval5 (a : ℝ) (h : rf1388.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1388.eval a=evalQPoly n5 a/evalQPoly den a := by
  change (evalQPoly rf1388.rational a+Real.sqrt 2*evalQPoly rf1388.irrational a)/evalQPoly rf1388.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n5,den,rf1388,rf1315]
  all_goals ring
#print axioms eval5

def n6 : Polynomial ℚ := Polynomial.C (1/10948 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/782 : ℚ)*Polynomial.X^1 + Polynomial.C (-3/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (1168/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-2735/5474 : ℚ)*Polynomial.X^4 + Polynomial.C (11003/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (12321/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (-180298/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (1635601/54740 : ℚ)*Polynomial.X^8 + Polynomial.C (-1045259/27370 : ℚ)*Polynomial.X^9 + Polynomial.C (1286277/54740 : ℚ)*Polynomial.X^10 + Polynomial.C (-294/115 : ℚ)*Polynomial.X^11
theorem eval6 (a : ℝ) (h : rf1441.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1441.eval a=evalQPoly n6 a/evalQPoly den a := by
  change (evalQPoly rf1441.rational a+Real.sqrt 2*evalQPoly rf1441.irrational a)/evalQPoly rf1441.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n6,den,rf1441,rf1315]
  all_goals ring
#print axioms eval6

def n7 : Polynomial ℚ := Polynomial.C (-1/15640 : ℚ)*Polynomial.X^0 + Polynomial.C (3/3220 : ℚ)*Polynomial.X^1 + Polynomial.C (-13/10948 : ℚ)*Polynomial.X^2 + Polynomial.C (-2393/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (4673/15640 : ℚ)*Polynomial.X^4 + Polynomial.C (-3499/3910 : ℚ)*Polynomial.X^5 + Polynomial.C (53321/27370 : ℚ)*Polynomial.X^6 + Polynomial.C (-146269/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (1743527/109480 : ℚ)*Polynomial.X^8 + Polynomial.C (-1959961/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (162431/3220 : ℚ)*Polynomial.X^10 + Polynomial.C (-2228909/54740 : ℚ)*Polynomial.X^11 + Polynomial.C (320223/15640 : ℚ)*Polynomial.X^12
theorem eval7 (a : ℝ) (h : rf1405.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1405.eval a=evalQPoly n7 a/evalQPoly den a := by
  change (evalQPoly rf1405.rational a+Real.sqrt 2*evalQPoly rf1405.irrational a)/evalQPoly rf1405.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n7,den,rf1405,rf1315]
  all_goals ring
#print axioms eval7

def n8 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-3/13685 : ℚ)*Polynomial.X^1 + Polynomial.C (53/13685 : ℚ)*Polynomial.X^2 + Polynomial.C (-226/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-58/805 : ℚ)*Polynomial.X^4 + Polynomial.C (11748/13685 : ℚ)*Polynomial.X^5 + Polynomial.C (-40424/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (10670/2737 : ℚ)*Polynomial.X^7 + Polynomial.C (45674/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-54541/2737 : ℚ)*Polynomial.X^9 + Polynomial.C (48133/1955 : ℚ)*Polynomial.X^10 + Polynomial.C (-11452/1955 : ℚ)*Polynomial.X^11
theorem eval8 (a : ℝ) (h : rf1459.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1459.eval a=evalQPoly n8 a/evalQPoly den a := by
  change (evalQPoly rf1459.rational a+Real.sqrt 2*evalQPoly rf1459.irrational a)/evalQPoly rf1459.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n8,den,rf1459,rf1315]
  all_goals ring
#print axioms eval8

def n9 : Polynomial ℚ := Polynomial.C (1/7820 : ℚ)*Polynomial.X^0 + Polynomial.C (-5/2737 : ℚ)*Polynomial.X^1 + Polynomial.C (81/54740 : ℚ)*Polynomial.X^2 + Polynomial.C (1286/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-467/782 : ℚ)*Polynomial.X^4 + Polynomial.C (4372/2737 : ℚ)*Polynomial.X^5 + Polynomial.C (-16367/5474 : ℚ)*Polynomial.X^6 + Polynomial.C (14502/1955 : ℚ)*Polynomial.X^7 + Polynomial.C (-5509/340 : ℚ)*Polynomial.X^8 + Polynomial.C (258981/13685 : ℚ)*Polynomial.X^9 + Polynomial.C (-841/92 : ℚ)*Polynomial.X^10
theorem eval9 (a : ℝ) (h : rf1495.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1495.eval a=evalQPoly n9 a/evalQPoly den a := by
  change (evalQPoly rf1495.rational a+Real.sqrt 2*evalQPoly rf1495.irrational a)/evalQPoly rf1495.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n9,den,rf1495,rf1315]
  all_goals ring
#print axioms eval9

def n10 : Polynomial ℚ := Polynomial.C (-1/27370 : ℚ)*Polynomial.X^0 + Polynomial.C (27/54740 : ℚ)*Polynomial.X^1 + Polynomial.C (-1/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-1299/54740 : ℚ)*Polynomial.X^3 + Polynomial.C (279/2737 : ℚ)*Polynomial.X^4 + Polynomial.C (-2593/27370 : ℚ)*Polynomial.X^5 + Polynomial.C (3967/13685 : ℚ)*Polynomial.X^6 + Polynomial.C (-82347/27370 : ℚ)*Polynomial.X^7 + Polynomial.C (26573/3910 : ℚ)*Polynomial.X^8 + Polynomial.C (129207/54740 : ℚ)*Polynomial.X^9 + Polynomial.C (-112219/3910 : ℚ)*Polynomial.X^10 + Polynomial.C (265503/7820 : ℚ)*Polynomial.X^11
theorem eval10 (a : ℝ) (h : rf1476.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1476.eval a=evalQPoly n10 a/evalQPoly den a := by
  change (evalQPoly rf1476.rational a+Real.sqrt 2*evalQPoly rf1476.irrational a)/evalQPoly rf1476.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n10,den,rf1476,rf1315]
  all_goals ring
#print axioms eval10

def n11 : Polynomial ℚ := Polynomial.C (0 : ℚ)*Polynomial.X^0 + Polynomial.C (-1/5474 : ℚ)*Polynomial.X^1 + Polynomial.C (103/27370 : ℚ)*Polynomial.X^2 + Polynomial.C (-228/13685 : ℚ)*Polynomial.X^3 + Polynomial.C (-1216/13685 : ℚ)*Polynomial.X^4 + Polynomial.C (1917/1955 : ℚ)*Polynomial.X^5 + Polynomial.C (-6099/1955 : ℚ)*Polynomial.X^6 + Polynomial.C (46624/13685 : ℚ)*Polynomial.X^7 + Polynomial.C (64956/13685 : ℚ)*Polynomial.X^8 + Polynomial.C (-82479/3910 : ℚ)*Polynomial.X^9 + Polynomial.C (89789/3910 : ℚ)*Polynomial.X^10
theorem eval11 (a : ℝ) (h : rf1513.DefinedAt a) (hD : evalQPoly den a≠0) :
    rf1513.eval a=evalQPoly n11 a/evalQPoly den a := by
  change (evalQPoly rf1513.rational a+Real.sqrt 2*evalQPoly rf1513.irrational a)/evalQPoly rf1513.denominator a=_
  apply (div_eq_div_iff h hD).2
  norm_num [evalQPoly,n11,den,rf1513,rf1315]
  all_goals ring
#print axioms eval11


end Blueprint.Thomson.Finite.RFColumnProofs.Even044
