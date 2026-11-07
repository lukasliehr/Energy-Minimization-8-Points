import AllS.Units.N_FI.N_kernels.RFColumns.Even069_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even069.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(31/109480:ℚ),(-1/1190:ℚ),(-447/54740:ℚ),(2319/27370:ℚ),(-52427/109480:ℚ),(126447/54740:ℚ),(-6911/782:ℚ),(1315411/54740:ℚ),(-673473/15640:ℚ),(533794/13685:ℚ),(130447/7820:ℚ),(-44816/595:ℚ),(259811/6440:ℚ),(9713/460:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-9/54740:ℚ),(167/54740:ℚ),(-41/2380:ℚ),(-123/7820:ℚ),(8501/13685:ℚ),(-86661/27370:ℚ),(41173/5474:ℚ),(-150077/27370:ℚ),(-137639/7820:ℚ),(2982211/54740:ℚ),(-434853/7820:ℚ),(-14901/10948:ℚ),(323/10:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/15640:ℚ),(-53/54740:ℚ),(1/644:ℚ),(75/1564:ℚ),(-41427/109480:ℚ),(37531/27370:ℚ),(-815/238:ℚ),(217589/27370:ℚ),(-351219/21896:ℚ),(1021327/54740:ℚ),(-17213/7820:ℚ),(-741563/54740:ℚ),(841/184:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/13685:ℚ),(-13/13685:ℚ),(3/1955:ℚ),(12/805:ℚ),(18/805:ℚ),(-1726/2737:ℚ),(330/161:ℚ),(-27588/13685:ℚ),(-45139/13685:ℚ),(180539/13685:ℚ),(-1521/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n3]
  all_goals ring
def num004 : List ℚ := [(1/54740:ℚ),(-9/27370:ℚ),(137/109480:ℚ),(3/230:ℚ),(-1755/10948:ℚ),(3019/3910:ℚ),(-9957/4760:ℚ),(63/17:ℚ),(-349873/54740:ℚ),(434453/27370:ℚ),(-4036173/109480:ℚ),(200603/3910:ℚ),(-44841/3220:ℚ),(-1860977/27370:ℚ),(70849/920:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(26/13685:ℚ),(-223/27370:ℚ),(-379/10948:ℚ),(9999/13685:ℚ),(-12056/2737:ℚ),(184811/13685:ℚ),(-208433/10948:ℚ),(-37473/3910:ℚ),(238318/2737:ℚ),(-563617/3910:ℚ),(42077/460:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n5]
  all_goals ring
def num006 : List ℚ := [(-1/15640:ℚ),(27/27370:ℚ),(-37/27370:ℚ),(-771/13685:ℚ),(47809/109480:ℚ),(-18679/13685:ℚ),(23938/13685:ℚ),(72/1955:ℚ),(537/952:ℚ),(-381573/27370:ℚ),(878681/27370:ℚ),(-356553/13685:ℚ),(4077/920:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n6]
  all_goals ring
def num007 : List ℚ := [(1/21896:ℚ),(-2/2737:ℚ),(15/10948:ℚ),(2201/54740:ℚ),(-37993/109480:ℚ),(1945/1564:ℚ),(-53471/27370:ℚ),(-27219/27370:ℚ),(1344579/109480:ℚ),(-131679/3910:ℚ),(3241667/54740:ℚ),(-720071/10948:ℚ),(857165/21896:ℚ),(-6567/460:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(5/10948:ℚ),(-213/54740:ℚ),(117/54740:ℚ),(4619/27370:ℚ),(-31267/27370:ℚ),(18119/5474:ℚ),(-20151/5474:ℚ),(-271221/54740:ℚ),(248361/10948:ℚ),(-1466769/54740:ℚ),(2999/460:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n8]
  all_goals ring
def num009 : List ℚ := [(-1/10948:ℚ),(73/54740:ℚ),(-33/54740:ℚ),(-55/644:ℚ),(15839/27370:ℚ),(-38963/27370:ℚ),(-125/5474:ℚ),(222661/27370:ℚ),(-1119193/54740:ℚ),(276825/10948:ℚ),(-42283/2380:ℚ),(611/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n9]
  all_goals ring
def num010 : List ℚ := [(3/109480:ℚ),(-11/27370:ℚ),(0/1:ℚ),(384/13685:ℚ),(-19169/109480:ℚ),(855/2737:ℚ),(1359/1955:ℚ),(-53594/13685:ℚ),(658817/109480:ℚ),(-2103/5474:ℚ),(-182253/13685:ℚ),(11346/391:ℚ),(-26453/920:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(6/13685:ℚ),(-53/27370:ℚ),(-2/391:ℚ),(1997/13685:ℚ),(-12762/13685:ℚ),(37189/13685:ℚ),(-41586/13685:ℚ),(-115657/27370:ℚ),(39316/1955:ℚ),(-5187/230:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even069.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even069.den,Blueprint.Thomson.Finite.RFCatalogue.rf1661]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even069.PairData
