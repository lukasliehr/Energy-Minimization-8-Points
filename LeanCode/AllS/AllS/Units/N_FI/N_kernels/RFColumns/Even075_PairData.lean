import AllS.Units.N_FI.N_kernels.RFColumns.Even075_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even075.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/109480:ℚ),(-3/13685:ℚ),(37/27370:ℚ),(389/54740:ℚ),(-14363/109480:ℚ),(2159/3220:ℚ),(-19902/13685:ℚ),(1363/3910:ℚ),(482491/109480:ℚ),(-5825/782:ℚ),(50039/27370:ℚ),(52461/10948:ℚ),(-205601/109480:ℚ),(-91197/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-1/3220:ℚ),(39/54740:ℚ),(963/54740:ℚ),(-2182/13685:ℚ),(2977/5474:ℚ),(-15569/27370:ℚ),(-36543/27370:ℚ),(230249/54740:ℚ),(-148377/54740:ℚ),(-130453/54740:ℚ),(89499/54740:ℚ),(319/170:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-2/13685:ℚ),(3/10948:ℚ),(22/2737:ℚ),(-7453/109480:ℚ),(88/391:ℚ),(-1335/5474:ℚ),(-1236/2737:ℚ),(145079/109480:ℚ),(-2798/13685:ℚ),(-13791/7820:ℚ),(1478/2737:ℚ),(1201/1288:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-1/1955:ℚ),(19/13685:ℚ),(61/13685:ℚ),(52/13685:ℚ),(-2197/13685:ℚ),(3469/13685:ℚ),(6751/13685:ℚ),(-223/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(41/109480:ℚ),(-99/54740:ℚ),(-194/13685:ℚ),(5637/27370:ℚ),(-22315/21896:ℚ),(413/170:ℚ),(-24593/13685:ℚ),(-280877/54740:ℚ),(73789/4760:ℚ),(-38481/2380:ℚ),(1209/391:ℚ),(93589/13685:ℚ),(-439181/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(9/27370:ℚ),(-31/27370:ℚ),(-12/805:ℚ),(263/1564:ℚ),(-2020/2737:ℚ),(21159/13685:ℚ),(-7823/13685:ℚ),(-262671/54740:ℚ),(307943/27370:ℚ),(-245447/27370:ℚ),(-25289/13685:ℚ),(42781/7820:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n5]
  all_goals ring
def num006 : List ℚ := [(-1/109480:ℚ),(9/54740:ℚ),(-8/13685:ℚ),(-401/54740:ℚ),(9351/109480:ℚ),(-10371/27370:ℚ),(10159/13685:ℚ),(1439/27370:ℚ),(-320323/109480:ℚ),(242093/54740:ℚ),(-9111/13685:ℚ),(-171613/54740:ℚ),(12141/6440:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-9/54740:ℚ),(8/13685:ℚ),(11/1564:ℚ),(-8927/109480:ℚ),(1493/3910:ℚ),(-2755/2737:ℚ),(39229/27370:ℚ),(20467/109480:ℚ),(-350373/54740:ℚ),(204919/13685:ℚ),(-785291/54740:ℚ),(102251/109480:ℚ),(73062/13685:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(1/3220:ℚ),(-47/54740:ℚ),(-827/54740:ℚ),(821/5474:ℚ),(-16503/27370:ℚ),(31859/27370:ℚ),(-10547/27370:ℚ),(-26103/7820:ℚ),(12335/1564:ℚ),(-57729/7820:ℚ),(16807/7820:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(1/3220:ℚ),(-41/54740:ℚ),(-911/54740:ℚ),(825/5474:ℚ),(-14137/27370:ℚ),(3373/5474:ℚ),(24651/27370:ℚ),(-207241/54740:ℚ),(48541/10948:ℚ),(-3769/3220:ℚ),(-731/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n9]
  all_goals ring
def num010 : List ℚ := [(1/109480:ℚ),(-1/7820:ℚ),(-3/27370:ℚ),(531/54740:ℚ),(-5507/109480:ℚ),(397/27370:ℚ),(7748/13685:ℚ),(-40837/27370:ℚ),(-257/21896:ℚ),(274077/54740:ℚ),(-157253/27370:ℚ),(-97721/54740:ℚ),(69761/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(1/27370:ℚ),(-1/1955:ℚ),(1/27370:ℚ),(89/2737:ℚ),(-403/1955:ℚ),(6633/13685:ℚ),(-295/2737:ℚ),(-22637/13685:ℚ),(81729/27370:ℚ),(-2986/2737:ℚ),(-4661/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even075.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even075.den,Blueprint.Thomson.Finite.RFCatalogue.rf1667]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even075.PairData
