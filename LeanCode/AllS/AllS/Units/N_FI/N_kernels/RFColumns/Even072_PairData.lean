import AllS.Units.N_FI.N_kernels.RFColumns.Even072_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even072.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/6440:ℚ),(5/10948:ℚ),(199/27370:ℚ),(-8443/109480:ℚ),(1657/4760:ℚ),(-48179/54740:ℚ),(16256/13685:ℚ),(-39621/109480:ℚ),(-124371/109480:ℚ),(85567/54740:ℚ),(-108543/27370:ℚ),(175017/15640:ℚ),(-136269/15640:ℚ),(-175381/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(3/27370:ℚ),(-24/13685:ℚ),(13/1610:ℚ),(74/13685:ℚ),(-1614/13685:ℚ),(57/805:ℚ),(14976/13685:ℚ),(-4077/1955:ℚ),(-69519/27370:ℚ),(117403/13685:ℚ),(-14517/27370:ℚ),(-699/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-3/109480:ℚ),(6/13685:ℚ),(-43/54740:ℚ),(-48/1955:ℚ),(3201/15640:ℚ),(-9217/13685:ℚ),(4601/5474:ℚ),(7391/13685:ℚ),(-49305/21896:ℚ),(19991/13685:ℚ),(-75807/54740:ℚ),(8593/2737:ℚ),(-1227/1288:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(3/2737:ℚ),(-41/13685:ℚ),(-73/2737:ℚ),(1/5:ℚ),(-1077/1955:ℚ),(1291/1955:ℚ),(10273/13685:ℚ),(-58516/13685:ℚ),(528/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n3]
  all_goals ring
def num004 : List ℚ := [(-1/109480:ℚ),(19/109480:ℚ),(-83/109480:ℚ),(-88/13685:ℚ),(9839/109480:ℚ),(-51669/109480:ℚ),(150733/109480:ℚ),(-29861/13685:ℚ),(8707/15640:ℚ),(7221/1288:ℚ),(-1343793/109480:ℚ),(139453/13685:ℚ),(-50917/15640:ℚ),(901673/109480:ℚ),(-1467273/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/27370:ℚ),(1/2737:ℚ),(1/2737:ℚ),(-3/170:ℚ),(1026/13685:ℚ),(3/805:ℚ),(-621/595:ℚ),(51378/13685:ℚ),(-120291/27370:ℚ),(-82464/13685:ℚ),(45466/1955:ℚ),(-79751/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n5]
  all_goals ring
def num006 : List ℚ := [(3/109480:ℚ),(-13/27370:ℚ),(37/27370:ℚ),(647/27370:ℚ),(-25713/109480:ℚ),(12417/13685:ℚ),(-20558/13685:ℚ),(-3863/13685:ℚ),(551681/109480:ℚ),(-27539/3910:ℚ),(16411/5474:ℚ),(-671/1190:ℚ),(9053/6440:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n6]
  all_goals ring
def num007 : List ℚ := [(-1/54740:ℚ),(1/3220:ℚ),(-1/1190:ℚ),(-6/391:ℚ),(8191/54740:ℚ),(-32001/54740:ℚ),(14853/13685:ℚ),(-6864/13685:ℚ),(-6443/3220:ℚ),(363479/54740:ℚ),(-4575/322:ℚ),(13894/805:ℚ),(-3429/460:ℚ),(37129/54740:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(11/13685:ℚ),(-163/13685:ℚ),(141/1955:ℚ),(-3267/13685:ℚ),(33/85:ℚ),(915/2737:ℚ),(-1983/805:ℚ),(845/391:ℚ),(2744/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n8]
  all_goals ring
def num009 : List ℚ := [(1/27370:ℚ),(-31/54740:ℚ),(1/1190:ℚ),(1753/54740:ℚ),(-3484/13685:ℚ),(22007/27370:ℚ),(-11486/13685:ℚ),(-47349/27370:ℚ),(172383/27370:ℚ),(-379647/54740:ℚ),(9307/3910:ℚ),(61/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n9]
  all_goals ring
def num010 : List ℚ := [(-1/109480:ℚ),(2/13685:ℚ),(-1/5474:ℚ),(-127/13685:ℚ),(7467/109480:ℚ),(-1964/13685:ℚ),(-246/805:ℚ),(25794/13685:ℚ),(-47967/21896:ℚ),(-35822/13685:ℚ),(1691/238:ℚ),(-75819/13685:ℚ),(67143/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(3/27370:ℚ),(-29/27370:ℚ),(-39/13685:ℚ),(191/2737:ℚ),(-760/2737:ℚ),(1522/13685:ℚ),(22543/13685:ℚ),(-38987/13685:ℚ),(-58403/27370:ℚ),(23967/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even072.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even072.den,Blueprint.Thomson.Finite.RFCatalogue.rf1664]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even072.PairData
