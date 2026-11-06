import AllS.Units.N_FI.N_kernels.RFColumns.Even052_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even052.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/6440:ℚ),(1/1955:ℚ),(381/54740:ℚ),(-8509/109480:ℚ),(7605/21896:ℚ),(-45753/54740:ℚ),(29717/27370:ℚ),(-4359/15640:ℚ),(-35409/15640:ℚ),(150033/27370:ℚ),(-298199/54740:ℚ),(229933/109480:ℚ),(-2529/109480:ℚ),(-5427/7820:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-13/54740:ℚ),(1/13685:ℚ),(198/13685:ℚ),(-2773/27370:ℚ),(3883/13685:ℚ),(-5023/27370:ℚ),(-3393/3910:ℚ),(116303/54740:ℚ),(-65371/54740:ℚ),(-2283/1610:ℚ),(8759/5474:ℚ),(547/1190:ℚ),(-61/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-13/54740:ℚ),(-9/54740:ℚ),(831/54740:ℚ),(-337/3910:ℚ),(5907/27370:ℚ),(-2089/5474:ℚ),(22579/27370:ℚ),(-66531/54740:ℚ),(11911/54740:ℚ),(8599/10948:ℚ),(-7/92:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-8/13685:ℚ),(26/13685:ℚ),(24/1955:ℚ),(-1209/13685:ℚ),(1864/13685:ℚ),(2306/13685:ℚ),(-7848/13685:ℚ),(79/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n3]
  all_goals ring
def num004 : List ℚ := [(-1/109480:ℚ),(2/13685:ℚ),(-43/109480:ℚ),(-11/1610:ℚ),(7559/109480:ℚ),(-4118/13685:ℚ),(85469/109480:ℚ),(-160/119:ℚ),(137741/109480:ℚ),(16693/13685:ℚ),(-764417/109480:ℚ),(68175/5474:ℚ),(-1314739/109480:ℚ),(87383/13685:ℚ),(-33191/15640:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n4]
  all_goals ring
def num005 : List ℚ := [(-1/54740:ℚ),(13/54740:ℚ),(-2/13685:ℚ),(-11/805:ℚ),(563/5474:ℚ),(-9431/27370:ℚ),(14537/27370:ℚ),(2493/27370:ℚ),(-16333/7820:ℚ),(237259/54740:ℚ),(-6277/1610:ℚ),(-2083/5474:ℚ),(103711/27370:ℚ),(-8299/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(12/13685:ℚ),(3/1610:ℚ),(-38/595:ℚ),(778/2737:ℚ),(-142/595:ℚ),(-17237/13685:ℚ),(9290/2737:ℚ),(-8105/2737:ℚ),(314/391:ℚ),(9/230:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-3/21896:ℚ),(1/7820:ℚ),(463/54740:ℚ),(-6661/109480:ℚ),(16839/109480:ℚ),(491/27370:ℚ),(-24729/27370:ℚ),(36147/21896:ℚ),(60407/109480:ℚ),(-341469/54740:ℚ),(489331/54740:ℚ),(-32587/6440:ℚ),(24071/15640:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/27370:ℚ),(-6/13685:ℚ),(-3/27370:ℚ),(747/27370:ℚ),(-4997/27370:ℚ),(14249/27370:ℚ),(-13689/27370:ℚ),(-711/782:ℚ),(43052/13685:ℚ),(-99697/27370:ℚ),(3692/1955:ℚ),(-679/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(1/3220:ℚ),(-39/54740:ℚ),(-929/54740:ℚ),(4059/27370:ℚ),(-1897/3910:ℚ),(3117/5474:ℚ),(12867/27370:ℚ),(-15763/7820:ℚ),(133341/54740:ℚ),(-82251/54740:ℚ),(9/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n9]
  all_goals ring
def num010 : List ℚ := [(1/54740:ℚ),(-1/3910:ℚ),(3/13685:ℚ),(411/27370:ℚ),(-6073/54740:ℚ),(272/805:ℚ),(-1171/2737:ℚ),(-58/391:ℚ),(86883/54740:ℚ),(-93073/27370:ℚ),(46756/13685:ℚ),(-36167/27370:ℚ),(5091/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n10]
  all_goals ring
def num011 : List ℚ := [(1/27370:ℚ),(-11/27370:ℚ),(-1/1610:ℚ),(751/27370:ℚ),(-4133/27370:ℚ),(1193/3910:ℚ),(3483/27370:ℚ),(-44649/27370:ℚ),(32036/13685:ℚ),(5792/13685:ℚ),(-48759/13685:ℚ),(4149/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even052.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even052.den,Blueprint.Thomson.Finite.RFCatalogue.rf1323]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even052.PairData
