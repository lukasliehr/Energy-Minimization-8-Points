import AllS.Units.N_FI.N_kernels.RFColumns.Even079_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even079.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(11/109480:ℚ),(-83/54740:ℚ),(321/109480:ℚ),(443/5474:ℚ),(-79053/109480:ℚ),(35883/13685:ℚ),(-420323/109480:ℚ),(-7207/2380:ℚ),(460485/21896:ℚ),(-79493/2380:ℚ),(17057/952:ℚ),(239993/13685:ℚ),(-527633/15640:ℚ),(407317/27370:ℚ),(351919/109480:ℚ),(-205633/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-9/54740:ℚ),(81/109480:ℚ),(59/10948:ℚ),(-4579/54740:ℚ),(13301/27370:ℚ),(-44571/27370:ℚ),(176021/54740:ℚ),(-141/56:ℚ),(-280269/54740:ℚ),(440101/21896:ℚ),(-1802599/54740:ℚ),(12362/391:ℚ),(-226679/13685:ℚ),(15541/10948:ℚ),(183283/54740:ℚ),(-229/170:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/109480:ℚ),(2/13685:ℚ),(-1/4760:ℚ),(-239/27370:ℚ),(7167/109480:ℚ),(-2339/13685:ℚ),(9069/109480:ℚ),(2004/13685:ℚ),(86413/109480:ℚ),(-29093/13685:ℚ),(-93053/109480:ℚ),(29755/5474:ℚ),(-82191/21896:ℚ),(-38/595:ℚ),(1355/1288:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-2/13685:ℚ),(2/805:ℚ),(-194/13685:ℚ),(402/13685:ℚ),(106/13685:ℚ),(-1514/13685:ℚ),(1882/13685:ℚ),(-6/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-3/27370:ℚ),(37/21896:ℚ),(-13/3220:ℚ),(-9077/109480:ℚ),(22201/27370:ℚ),(-368349/109480:ℚ),(386877/54740:ℚ),(-13525/3128:ℚ),(-444457/27370:ℚ),(5557271/109480:ℚ),(-3760731/54740:ℚ),(4562373/109480:ℚ),(422827/27370:ℚ),(-1152887/21896:ℚ),(2212491/54740:ℚ),(-1314769/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n4]
  all_goals ring
def num005 : List ℚ := [(-1/109480:ℚ),(9/54740:ℚ),(-1/1288:ℚ),(-131/27370:ℚ),(97/1190:ℚ),(-1993/3910:ℚ),(52737/27370:ℚ),(-65236/13685:ℚ),(22319/3128:ℚ),(-26935/10948:ℚ),(-389961/21896:ℚ),(1458113/27370:ℚ),(-4658159/54740:ℚ),(1190292/13685:ℚ),(-3053833/54740:ℚ),(1699/85:ℚ),(-23051/7820:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/7820:ℚ),(-1/15640:ℚ),(7/782:ℚ),(-1067/21896:ℚ),(3011/54740:ℚ),(3407/15640:ℚ),(-4733/13685:ℚ),(-21571/15640:ℚ),(12991/3220:ℚ),(-244221/109480:ℚ),(-140283/27370:ℚ),(1203499/109480:ℚ),(-476779/54740:ℚ),(16299/6440:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-9/54740:ℚ),(83/109480:ℚ),(53/10948:ℚ),(-1779/21896:ℚ),(28131/54740:ℚ),(-209733/109480:ℚ),(45191/10948:ℚ),(-346933/109480:ℚ),(-417939/54740:ℚ),(574221/21896:ℚ),(-1995617/54740:ℚ),(2530547/109480:ℚ),(40373/10948:ℚ),(-1414479/109480:ℚ),(312037/54740:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/3220:ℚ),(67/54740:ℚ),(31/2737:ℚ),(-4241/27370:ℚ),(46479/54740:ℚ),(-21271/7820:ℚ),(4181/805:ℚ),(-211867/54740:ℚ),(-483039/54740:ℚ),(1838537/54740:ℚ),(-21076/391:ℚ),(680613/13685:ℚ),(-200089/7820:ℚ),(44443/7820:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(3/10948:ℚ),(-3/13685:ℚ),(-229/13685:ℚ),(6343/54740:ℚ),(-16433/54740:ℚ),(389/1955:ℚ),(7839/13685:ℚ),(-14241/7820:ℚ),(161593/54740:ℚ),(-5884/13685:ℚ),(-13082/1955:ℚ),(449809/54740:ℚ),(-2187/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(19/54740:ℚ),(-313/109480:ℚ),(-213/27370:ℚ),(24963/109480:ℚ),(-4223/3220:ℚ),(355423/109480:ℚ),(-24399/13685:ℚ),(-145893/15640:ℚ),(1337621/54740:ℚ),(-2625379/109480:ℚ),(-70957/27370:ℚ),(514519/15640:ℚ),(-1694841/54740:ℚ),(161979/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n10]
  all_goals ring
def num011 : List ℚ := [(1/54740:ℚ),(-4/13685:ℚ),(5/5474:ℚ),(2/161:ℚ),(-785/5474:ℚ),(418/595:ℚ),(-10411/5474:ℚ),(6635/2737:ℚ),(78053/54740:ℚ),(-153469/13685:ℚ),(542723/27370:ℚ),(-239261/13685:ℚ),(12913/1955:ℚ),(8943/13685:ℚ),(-3559/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.n11]
  all_goals ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even079.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even079.den,Blueprint.Thomson.Finite.RFCatalogue.rf1671]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even079.PairData
