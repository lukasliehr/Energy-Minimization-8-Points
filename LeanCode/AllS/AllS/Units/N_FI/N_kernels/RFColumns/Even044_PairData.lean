import AllS.Units.N_FI.N_kernels.RFColumns.Even044_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even044.PairData
def num000 : List ℚ := [(0/1:ℚ),(-3/109480:ℚ),(1/10948:ℚ),(163/27370:ℚ),(-891/13685:ℚ),(21101/109480:ℚ),(1541/2380:ℚ),(-96062/13685:ℚ),(363038/13685:ℚ),(-6122441/109480:ℚ),(3150067/54740:ℚ),(301377/27370:ℚ),(-1172327/13685:ℚ),(715913/15640:ℚ),(187891/7820:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-2/13685:ℚ),(79/27370:ℚ),(-7/391:ℚ),(-79/27370:ℚ),(1565/2737:ℚ),(-2531/805:ℚ),(106732/13685:ℚ),(-11819/1955:ℚ),(-242146/13685:ℚ),(89639/1610:ℚ),(-773711/13685:ℚ),(-39447/27370:ℚ),(2763/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(3/7820:ℚ),(-607/54740:ℚ),(467/7820:ℚ),(4909/27370:ℚ),(-79151/27370:ℚ),(323297/27370:ℚ),(-128671/5474:ℚ),(236129/10948:ℚ),(43529/54740:ℚ),(-116869/7820:ℚ),(363/92:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/13685:ℚ),(-13/13685:ℚ),(3/1955:ℚ),(12/805:ℚ),(18/805:ℚ),(-1726/2737:ℚ),(330/161:ℚ),(-27588/13685:ℚ),(-45139/13685:ℚ),(180539/13685:ℚ),(-1521/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n3]
  all_goals ring
def num004 : List ℚ := [(3/109480:ℚ),(-7/15640:ℚ),(43/54740:ℚ),(159/5474:ℚ),(-4101/15640:ℚ),(100091/109480:ℚ),(-2991/5474:ℚ),(-100386/13685:ℚ),(3508429/109480:ℚ),(-7680011/109480:ℚ),(950303/10948:ℚ),(-817447/27370:ℚ),(-8175757/109480:ℚ),(1337143/15640:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-3/27370:ℚ),(38/13685:ℚ),(-284/13685:ℚ),(61/27370:ℚ),(10721/13685:ℚ),(-3952/805:ℚ),(198036/13685:ℚ),(-52359/2737:ℚ),(-65851/5474:ℚ),(1249182/13685:ℚ),(-2014788/13685:ℚ),(361047/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n5]
  all_goals ring
def num006 : List ℚ := [(-1/10948:ℚ),(1/782:ℚ),(3/10948:ℚ),(-1168/13685:ℚ),(2735/5474:ℚ),(-11003/13685:ℚ),(-12321/5474:ℚ),(180298/13685:ℚ),(-1635601/54740:ℚ),(1045259/27370:ℚ),(-1286277/54740:ℚ),(294/115:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n6]
  all_goals ring
def num007 : List ℚ := [(1/15640:ℚ),(-3/3220:ℚ),(13/10948:ℚ),(2393/54740:ℚ),(-4673/15640:ℚ),(3499/3910:ℚ),(-53321/27370:ℚ),(146269/27370:ℚ),(-1743527/109480:ℚ),(1959961/54740:ℚ),(-162431/3220:ℚ),(2228909/54740:ℚ),(-320223/15640:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(3/13685:ℚ),(-53/13685:ℚ),(226/13685:ℚ),(58/805:ℚ),(-11748/13685:ℚ),(40424/13685:ℚ),(-10670/2737:ℚ),(-45674/13685:ℚ),(54541/2737:ℚ),(-48133/1955:ℚ),(11452/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n8]
  all_goals ring
def num009 : List ℚ := [(-1/7820:ℚ),(5/2737:ℚ),(-81/54740:ℚ),(-1286/13685:ℚ),(467/782:ℚ),(-4372/2737:ℚ),(16367/5474:ℚ),(-14502/1955:ℚ),(5509/340:ℚ),(-258981/13685:ℚ),(841/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n9]
  all_goals ring
def num010 : List ℚ := [(1/27370:ℚ),(-27/54740:ℚ),(1/27370:ℚ),(1299/54740:ℚ),(-279/2737:ℚ),(2593/27370:ℚ),(-3967/13685:ℚ),(82347/27370:ℚ),(-26573/3910:ℚ),(-129207/54740:ℚ),(112219/3910:ℚ),(-265503/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(1/5474:ℚ),(-103/27370:ℚ),(228/13685:ℚ),(1216/13685:ℚ),(-1917/1955:ℚ),(6099/1955:ℚ),(-46624/13685:ℚ),(-64956/13685:ℚ),(82479/3910:ℚ),(-89789/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even044.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even044.den,Blueprint.Thomson.Finite.RFCatalogue.rf1315]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even044.PairData
