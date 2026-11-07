import AllS.Units.N_FI.N_kernels.RFColumns.Even040_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even040.PairData
def num000 : List ℚ := [(0/1:ℚ),(39/109480:ℚ),(-177/27370:ℚ),(957/27370:ℚ),(-109/54740:ℚ),(-42029/109480:ℚ),(-64321/54740:ℚ),(7096/391:ℚ),(-1950833/27370:ℚ),(15430013/109480:ℚ),(-100613/805:ℚ),(-1376877/27370:ℚ),(11971263/54740:ℚ),(-13790199/109480:ℚ),(-2530169/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n0]
  all_goals ring
def num001 : List ℚ := [(2/13685:ℚ),(-36/13685:ℚ),(209/13685:ℚ),(-87/3910:ℚ),(-125/5474:ℚ),(-8123/13685:ℚ),(3876/805:ℚ),(-10179/805:ℚ),(76343/13685:ℚ),(24588/595:ℚ),(-1266681/13685:ℚ),(305667/5474:ℚ),(1694599/27370:ℚ),(-7801/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/13685:ℚ),(-7/7820:ℚ),(-39/2737:ℚ),(2979/7820:ℚ),(-9330/2737:ℚ),(84703/5474:ℚ),(-509178/13685:ℚ),(7077/170:ℚ),(3119/1955:ℚ),(-3276949/54740:ℚ),(22767/391:ℚ),(-4659/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n2]
  all_goals ring
def num003 : List ℚ := [(-2/13685:ℚ),(31/13685:ℚ),(-3/391:ℚ),(-638/13685:ℚ),(7088/13685:ℚ),(-34694/13685:ℚ),(106826/13685:ℚ),(-22432/1955:ℚ),(-17470/2737:ℚ),(710127/13685:ℚ),(-1145689/13685:ℚ),(6362/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n3]
  all_goals ring
def num004 : List ℚ := [(-1/15640:ℚ),(19/15640:ℚ),(-106/13685:ℚ),(-9/3910:ℚ),(6445/21896:ℚ),(-176247/109480:ℚ),(36881/13685:ℚ),(126878/13685:ℚ),(-6969173/109480:ℚ),(18694663/109480:ℚ),(-3396919/13685:ℚ),(3870259/27370:ℚ),(2543103/21896:ℚ),(-20268757/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-13/13685:ℚ),(347/27370:ℚ),(-197/2737:ℚ),(11663/27370:ℚ),(-43422/13685:ℚ),(214927/13685:ℚ),(-4834/115:ℚ),(614639/13685:ℚ),(119949/1955:ℚ),(-7562777/27370:ℚ),(761937/1955:ℚ),(-894859/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n5]
  all_goals ring
def num006 : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-1/161:ℚ),(346/2737:ℚ),(-50/119:ℚ),(-22128/13685:ℚ),(196086/13685:ℚ),(-548804/13685:ℚ),(771269/13685:ℚ),(-98020/2737:ℚ),(-8417/805:ℚ),(20434/805:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n6]
  all_goals ring
def num007 : List ℚ := [(-1/109480:ℚ),(-37/54740:ℚ),(449/27370:ℚ),(-367/3220:ℚ),(20523/109480:ℚ),(20143/27370:ℚ),(-14052/13685:ℚ),(-16417/1190:ℚ),(6815813/109480:ℚ),(-7040009/54740:ℚ),(3898439/27370:ℚ),(-3751651/54740:ℚ),(1951377/109480:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n7]
  all_goals ring
def num008 : List ℚ := [(-2/13685:ℚ),(33/13685:ℚ),(-297/27370:ℚ),(87/3910:ℚ),(-4702/13685:ℚ),(39072/13685:ℚ),(-123087/13685:ℚ),(17869/1955:ℚ),(197108/13685:ℚ),(-770269/13685:ℚ),(267177/3910:ℚ),(-83433/3910:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n8]
  all_goals ring
def num009 : List ℚ := [(1/54740:ℚ),(0/1:ℚ),(-99/7820:ℚ),(524/2737:ℚ),(-31531/27370:ℚ),(50684/13685:ℚ),(-250981/27370:ℚ),(303668/13685:ℚ),(-306253/7820:ℚ),(103556/2737:ℚ),(-10445/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n9]
  all_goals ring
def num010 : List ℚ := [(3/54740:ℚ),(-71/54740:ℚ),(773/54740:ℚ),(-3049/54740:ℚ),(-3889/27370:ℚ),(44621/27370:ℚ),(-80331/27370:ℚ),(-27445/5474:ℚ),(1106991/54740:ℚ),(-752291/54740:ℚ),(-43573/1564:ℚ),(428701/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(18/13685:ℚ),(-179/13685:ℚ),(892/13685:ℚ),(-7408/13685:ℚ),(46976/13685:ℚ),(-127758/13685:ℚ),(73796/13685:ℚ),(312952/13685:ℚ),(-111646/1955:ℚ),(103999/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even040.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even040.den,Blueprint.Thomson.Finite.RFCatalogue.rf1311]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even040.PairData
