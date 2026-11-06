import AllS.Units.N_FI.N_kernels.RFColumns.Even043_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even043.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-3/27370:ℚ),(117/54740:ℚ),(-71/5474:ℚ),(-39/54740:ℚ),(10539/27370:ℚ),(-63011/27370:ℚ),(14957/1955:ℚ),(-19309/1190:ℚ),(517511/27370:ℚ),(-27171/10948:ℚ),(-518939/27370:ℚ),(130265/10948:ℚ),(4051/782:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(3/3910:ℚ),(-15/2737:ℚ),(227/27370:ℚ),(61/595:ℚ),(-9599/13685:ℚ),(26578/13685:ℚ),(-25409/13685:ℚ),(-102829/27370:ℚ),(53487/3910:ℚ),(-201723/13685:ℚ),(-1/27370:ℚ),(144/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(11/54740:ℚ),(-48/13685:ℚ),(111/7820:ℚ),(1144/13685:ℚ),(-26561/27370:ℚ),(51584/13685:ℚ),(-205119/27370:ℚ),(100888/13685:ℚ),(-60633/54740:ℚ),(-10208/2737:ℚ),(135/92:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(9/10948:ℚ),(0/1:ℚ),(29/1610:ℚ),(-131/805:ℚ),(2521/5474:ℚ),(-1212/2737:ℚ),(-8383/10948:ℚ),(90053/27370:ℚ),(-317/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/2380:ℚ),(1/322:ℚ),(-13/54740:ℚ),(-7409/54740:ℚ),(26581/27370:ℚ),(-49481/13685:ℚ),(47247/5474:ℚ),(-812033/54740:ℚ),(978941/54740:ℚ),(-196179/27370:ℚ),(-180997/10948:ℚ),(31803/1564:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(41/54740:ℚ),(-3/595:ℚ),(159/54740:ℚ),(1977/13685:ℚ),(-25671/27370:ℚ),(40228/13685:ℚ),(-124077/27370:ℚ),(-5157/5474:ℚ),(60101/3220:ℚ),(-468283/13685:ℚ),(36089/1564:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(3/13685:ℚ),(1/1564:ℚ),(-29/1610:ℚ),(361/5474:ℚ),(229/1955:ℚ),(-38427/27370:ℚ),(59208/13685:ℚ),(-416937/54740:ℚ),(118434/13685:ℚ),(-57465/10948:ℚ),(31/46:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n6]
  all_goals ring
def num007 : List ℚ := [(1/54740:ℚ),(-3/10948:ℚ),(13/27370:ℚ),(653/54740:ℚ),(-283/3220:ℚ),(7929/27370:ℚ),(-10063/13685:ℚ),(11813/5474:ℚ),(-329757/54740:ℚ),(668509/54740:ℚ),(-421047/27370:ℚ),(565953/54740:ℚ),(-5987/1564:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(3/54740:ℚ),(-27/27370:ℚ),(281/54740:ℚ),(82/13685:ℚ),(-4461/27370:ℚ),(1353/1955:ℚ),(-1437/1190:ℚ),(-4286/13685:ℚ),(275591/54740:ℚ),(-27101/3910:ℚ),(2863/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n8]
  all_goals ring
def num009 : List ℚ := [(-1/27370:ℚ),(3/5474:ℚ),(-11/13685:ℚ),(-358/13685:ℚ),(509/2737:ℚ),(-7867/13685:ℚ),(2476/1955:ℚ),(-40118/13685:ℚ),(144743/27370:ℚ),(-5703/1190:ℚ),(33/23:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n9]
  all_goals ring
def num010 : List ℚ := [(1/54740:ℚ),(-1/3910:ℚ),(1/7820:ℚ),(369/27370:ℚ),(-301/3910:ℚ),(2013/13685:ℚ),(-2361/27370:ℚ),(4033/13685:ℚ),(-48219/54740:ℚ),(-27411/27370:ℚ),(356667/54740:ℚ),(-5841/782:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(1/13685:ℚ),(-31/27370:ℚ),(48/13685:ℚ),(76/2737:ℚ),(-3226/13685:ℚ),(9389/13685:ℚ),(-10656/13685:ℚ),(-12368/13685:ℚ),(67593/13685:ℚ),(-4561/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even043.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even043.den,Blueprint.Thomson.Finite.RFCatalogue.rf1314]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even043.PairData
