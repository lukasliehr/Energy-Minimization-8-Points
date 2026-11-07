import AllS.Units.N_FI.N_kernels.RFColumns.Even077_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even077.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(9/54740:ℚ),(-15/21896:ℚ),(-47/7820:ℚ),(9063/109480:ℚ),(-24359/54740:ℚ),(21987/15640:ℚ),(-148387/54740:ℚ),(223341/109480:ℚ),(275151/54740:ℚ),(-276007/15640:ℚ),(181123/7820:ℚ),(-1557683/109480:ℚ),(125423/54740:ℚ),(286471/109480:ℚ),(-7727/7820:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(3/10948:ℚ),(-3/5474:ℚ),(-197/13685:ℚ),(106/805:ℚ),(-13537/27370:ℚ),(20369/27370:ℚ),(4125/5474:ℚ),(-265927/54740:ℚ),(72825/10948:ℚ),(9992/13685:ℚ),(-58955/5474:ℚ),(117224/13685:ℚ),(25307/27370:ℚ),(-201/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-19/109480:ℚ),(9/13685:ℚ),(31/3910:ℚ),(-10011/109480:ℚ),(41801/109480:ℚ),(-1899/2737:ℚ),(1424/13685:ℚ),(183307/109480:ℚ),(-313377/109480:ℚ),(54/23:ℚ),(-4965/5474:ℚ),(-33937/109480:ℚ),(9/184:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-8/13685:ℚ),(26/13685:ℚ),(24/1955:ℚ),(-1209/13685:ℚ),(1864/13685:ℚ),(2306/13685:ℚ),(-7848/13685:ℚ),(79/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n3]
  all_goals ring
def num004 : List ℚ := [(1/109480:ℚ),(-9/54740:ℚ),(39/54740:ℚ),(611/109480:ℚ),(-8937/109480:ℚ),(6357/13685:ℚ),(-21989/13685:ℚ),(79377/21896:ℚ),(-496793/109480:ℚ),(-60897/54740:ℚ),(193643/10948:ℚ),(-850783/21896:ℚ),(5239617/109480:ℚ),(-995837/27370:ℚ),(466363/27370:ℚ),(-54811/15640:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n4]
  all_goals ring
def num005 : List ℚ := [(1/54740:ℚ),(-3/10948:ℚ),(1/1610:ℚ),(8/595:ℚ),(-1798/13685:ℚ),(15143/27370:ℚ),(-15902/13685:ℚ),(12113/27370:ℚ),(6441/1564:ℚ),(-603049/54740:ℚ),(144699/13685:ℚ),(111847/27370:ℚ),(-273857/13685:ℚ),(14543/782:ℚ),(-23709/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n5]
  all_goals ring
def num006 : List ℚ := [(-1/109480:ℚ),(19/109480:ℚ),(-37/54740:ℚ),(-59/7820:ℚ),(9837/109480:ℚ),(-43851/109480:ℚ),(24733/27370:ℚ),(-23447/27370:ℚ),(-99063/109480:ℚ),(496957/109480:ℚ),(-408277/54740:ℚ),(19851/3220:ℚ),(-271861/109480:ℚ),(381/920:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(4/13685:ℚ),(-2/2737:ℚ),(-79/5474:ℚ),(1525/10948:ℚ),(-15429/27370:ℚ),(16659/13685:ℚ),(-2236/1955:ℚ),(-96027/54740:ℚ),(121654/13685:ℚ),(-41789/2737:ℚ),(72831/5474:ℚ),(-350733/54740:ℚ),(3919/3910:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(13/27370:ℚ),(-3/27370:ℚ),(-813/27370:ℚ),(2819/13685:ℚ),(-647/1190:ℚ),(2451/27370:ℚ),(76079/27370:ℚ),(-15968/2737:ℚ),(23652/13685:ℚ),(7402/805:ℚ),(-178427/13685:ℚ),(21297/3910:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/7820:ℚ),(87/54740:ℚ),(147/7820:ℚ),(-5791/27370:ℚ),(3001/3910:ℚ),(-22453/27370:ℚ),(-44923/27370:ℚ),(57737/10948:ℚ),(-60933/10948:ℚ),(157603/54740:ℚ),(-37/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n9]
  all_goals ring
def num010 : List ℚ := [(-1/109480:ℚ),(3/21896:ℚ),(-1/2380:ℚ),(-279/54740:ℚ),(401/6440:ℚ),(-5677/15640:ℚ),(37701/27370:ℚ),(-17091/5474:ℚ),(237849/109480:ℚ),(116407/15640:ℚ),(-67603/3220:ℚ),(181699/7820:ℚ),(-1452569/109480:ℚ),(44797/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n10]
  all_goals ring
def num011 : List ℚ := [(-1/27370:ℚ),(13/27370:ℚ),(-3/13685:ℚ),(-771/27370:ℚ),(563/2737:ℚ),(-17473/27370:ℚ),(19137/27370:ℚ),(34163/27370:ℚ),(-66646/13685:ℚ),(2004/391:ℚ),(1373/5474:ℚ),(-2326/595:ℚ),(7493/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even077.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even077.den,Blueprint.Thomson.Finite.RFCatalogue.rf1669]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even077.PairData
