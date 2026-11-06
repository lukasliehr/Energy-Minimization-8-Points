import AllS.Units.N_FI.N_kernels.RFColumns.Even059_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even059.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(1/1288:ℚ),(-1/170:ℚ),(781/54740:ℚ),(888/13685:ℚ),(-76569/109480:ℚ),(89781/27370:ℚ),(-268649/27370:ℚ),(96395/5474:ℚ),(-1069021/109480:ℚ),(-995447/27370:ℚ),(1145281/10948:ℚ),(-1648567/13685:ℚ),(5526177/109480:ℚ),(38973/3910:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n0]
  all_goals ring
def num001 : List ℚ := [(-1/54740:ℚ),(41/109480:ℚ),(-59/21896:ℚ),(41/7820:ℚ),(2347/54740:ℚ),(-8593/21896:ℚ),(185037/109480:ℚ),(-119597/27370:ℚ),(288161/54740:ℚ),(620343/109480:ℚ),(-719017/21896:ℚ),(3407/68:ℚ),(-261775/10948:ℚ),(-326909/15640:ℚ),(17479/680:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n1]
  all_goals ring
def num002 : List ℚ := [(-1/109480:ℚ),(3/13685:ℚ),(-19/10948:ℚ),(11/27370:ℚ),(57/680:ℚ),(-1759/2737:ℚ),(68823/27370:ℚ),(-16119/2737:ℚ),(744689/109480:ℚ),(64371/13685:ℚ),(-341123/10948:ℚ),(272807/5474:ℚ),(-4003913/109480:ℚ),(203/23:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n2]
  all_goals ring
def num003 : List ℚ := [(1/109480:ℚ),(-3/27370:ℚ),(1/13685:ℚ),(18/13685:ℚ),(343/15640:ℚ),(-650/2737:ℚ),(13154/13685:ℚ),(-4017/1955:ℚ),(173163/109480:ℚ),(111847/27370:ℚ),(-188327/13685:ℚ),(35091/1955:ℚ),(-9723/920:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/21896:ℚ),(-1/340:ℚ),(113/1955:ℚ),(-537/1190:ℚ),(209721/109480:ℚ),(-116033/27370:ℚ),(20597/13685:ℚ),(968741/54740:ℚ),(-1083097/21896:ℚ),(3040339/54740:ℚ),(-41716/13685:ℚ),(-169982/2737:ℚ),(854613/15640:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n4]
  all_goals ring
def num005 : List ℚ := [(-1/109480:ℚ),(1/3220:ℚ),(-5/1564:ℚ),(6/595:ℚ),(819/15640:ℚ),(-36399/54740:ℚ),(91269/27370:ℚ),(-1148/115:ℚ),(260583/15640:ℚ),(-10973/3220:ℚ),(-2900171/54740:ℚ),(1736694/13685:ℚ),(-2162243/15640:ℚ),(519309/7820:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n5]
  all_goals ring
def num006 : List ℚ := [(-1/109480:ℚ),(1/7820:ℚ),(1/2737:ℚ),(-727/54740:ℚ),(297/4760:ℚ),(-341/27370:ℚ),(-6539/13685:ℚ),(2845/5474:ℚ),(277677/109480:ℚ),(-87145/10948:ℚ),(127814/13685:ℚ),(-2095/644:ℚ),(-1853/920:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-1/10948:ℚ),(-61/54740:ℚ),(571/27370:ℚ),(-1927/15640:ℚ),(3919/10948:ℚ),(-14403/27370:ℚ),(-273/1955:ℚ),(355807/109480:ℚ),(-484751/54740:ℚ),(30517/2380:ℚ),(-332501/27370:ℚ),(857809/109480:ℚ),(-39969/7820:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n7]
  all_goals ring
def num008 : List ℚ := [(3/109480:ℚ),(-29/54740:ℚ),(83/27370:ℚ),(121/54740:ℚ),(-11561/109480:ℚ),(16757/27370:ℚ),(-26836/13685:ℚ),(89819/27370:ℚ),(14849/109480:ℚ),(-94171/7820:ℚ),(28011/1190:ℚ),(-154313/7820:ℚ),(66451/15640:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(31/13685:ℚ),(-319/13685:ℚ),(177/1955:ℚ),(-587/13685:ℚ),(-209/391:ℚ),(18409/13685:ℚ),(-27099/13685:ℚ),(9616/2737:ℚ),(-56072/13685:ℚ),(38/23:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n9]
  all_goals ring
def num010 : List ℚ := [(1/109480:ℚ),(-1/7820:ℚ),(-9/13685:ℚ),(1079/54740:ℚ),(-14591/109480:ℚ),(1699/3910:ℚ),(-9599/13685:ℚ),(-6841/27370:ℚ),(71397/15640:ℚ),(-30307/3220:ℚ),(35192/13685:ℚ),(816619/54740:ℚ),(-277971/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n10]
  all_goals ring
def num011 : List ℚ := [(1/54740:ℚ),(-13/27370:ℚ),(5/1564:ℚ),(1/595:ℚ),(-37/322:ℚ),(9113/13685:ℚ),(-8149/3910:ℚ),(45046/13685:ℚ),(53441/54740:ℚ),(-375813/27370:ℚ),(36749/1564:ℚ),(-32347/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even059.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even059.den,Blueprint.Thomson.Finite.RFCatalogue.rf1651]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even059.PairData
