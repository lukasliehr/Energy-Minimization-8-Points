import AllS.Units.N_FI.N_kernels.RFColumns.Even047_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even047.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/7820:ℚ),(3/13685:ℚ),(1/230:ℚ),(-691/21896:ℚ),(953/7820:ℚ),(-3627/13685:ℚ),(-7577/13685:ℚ),(599747/109480:ℚ),(-138109/10948:ℚ),(87104/13685:ℚ),(373291/27370:ℚ),(-1393157/109480:ℚ),(-13063/3220:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/13685:ℚ),(-39/27370:ℚ),(37/3910:ℚ),(-281/13685:ℚ),(-288/13685:ℚ),(19/391:ℚ),(951/1955:ℚ),(-14286/13685:ℚ),(-26157/13685:ℚ),(164973/27370:ℚ),(2103/5474:ℚ),(-37/5:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(5/10948:ℚ),(19/27370:ℚ),(-1707/54740:ℚ),(1861/13685:ℚ),(-163/27370:ℚ),(-18779/13685:ℚ),(14347/3910:ℚ),(-72441/27370:ℚ),(-178611/54740:ℚ),(27575/5474:ℚ),(-211/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(3/2737:ℚ),(-41/13685:ℚ),(-73/2737:ℚ),(1/5:ℚ),(-1077/1955:ℚ),(1291/1955:ℚ),(10273/13685:ℚ),(-58516/13685:ℚ),(528/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n3]
  all_goals ring
def num004 : List ℚ := [(-1/109480:ℚ),(1/6440:ℚ),(-5/10948:ℚ),(-389/54740:ℚ),(7961/109480:ℚ),(-1933/6440:ℚ),(3377/5474:ℚ),(-461/1190:ℚ),(-33347/21896:ℚ),(33729/4760:ℚ),(-915617/54740:ℚ),(966859/54740:ℚ),(337367/109480:ℚ),(-101179/6440:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-12/13685:ℚ),(199/27370:ℚ),(-402/13685:ℚ),(1557/13685:ℚ),(-8966/13685:ℚ),(33539/13685:ℚ),(-45646/13685:ℚ),(-123883/27370:ℚ),(330/17:ℚ),(-4123/230:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n5]
  all_goals ring
def num006 : List ℚ := [(1/27370:ℚ),(-1/1955:ℚ),(0/1:ℚ),(181/5474:ℚ),(-81/391:ℚ),(6334/13685:ℚ),(148/1955:ℚ),(-33479/13685:ℚ),(28249/5474:ℚ),(-56411/13685:ℚ),(-13528/13685:ℚ),(4477/1610:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n6]
  all_goals ring
def num007 : List ℚ := [(-3/109480:ℚ),(11/27370:ℚ),(-1/3910:ℚ),(-137/5474:ℚ),(19361/109480:ℚ),(-6751/13685:ℚ),(5352/13685:ℚ),(2689/2737:ℚ),(-44237/21896:ℚ),(-27613/27370:ℚ),(29163/5474:ℚ),(-128461/27370:ℚ),(19379/6440:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/27370:ℚ),(1/1190:ℚ),(-118/13685:ℚ),(824/13685:ℚ),(-4127/13685:ℚ),(11279/13685:ℚ),(-4702/13685:ℚ),(-6156/1955:ℚ),(137063/27370:ℚ),(-171/230:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n8]
  all_goals ring
def num009 : List ℚ := [(3/54740:ℚ),(-3/3910:ℚ),(-3/54740:ℚ),(6/119:ℚ),(-8609/27370:ℚ),(1957/2737:ℚ),(-197/1190:ℚ),(-24606/13685:ℚ),(112911/54740:ℚ),(24827/27370:ℚ),(-1227/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(13/54740:ℚ),(3/7820:ℚ),(-143/7820:ℚ),(2439/27370:ℚ),(-1707/27370:ℚ),(-2281/3910:ℚ),(35243/27370:ℚ),(8423/10948:ℚ),(-33857/7820:ℚ),(9477/10948:ℚ),(2357/460:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(18/13685:ℚ),(-12/1955:ℚ),(62/13685:ℚ),(-858/13685:ℚ),(8718/13685:ℚ),(-15212/13685:ℚ),(-28062/13685:ℚ),(573/115:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even047.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even047.den,Blueprint.Thomson.Finite.RFCatalogue.rf1318]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even047.PairData
