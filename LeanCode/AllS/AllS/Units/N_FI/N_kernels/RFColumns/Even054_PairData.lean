import AllS.Units.N_FI.N_kernels.RFColumns.Even054_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even054.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/109480:ℚ),(1/13685:ℚ),(71/109480:ℚ),(-63/7820:ℚ),(981/109480:ℚ),(4729/27370:ℚ),(-15587/21896:ℚ),(5507/54740:ℚ),(524833/109480:ℚ),(-137478/13685:ℚ),(24641/6440:ℚ),(75891/7820:ℚ),(-261841/21896:ℚ),(12671/3910:ℚ),(287223/109480:ℚ),(-30143/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(2/13685:ℚ),(-47/109480:ℚ),(-361/54740:ℚ),(3939/54740:ℚ),(-4502/13685:ℚ),(1237/1564:ℚ),(-3891/5474:ℚ),(-4559/3128:ℚ),(76736/13685:ℚ),(-809427/109480:ℚ),(9651/3220:ℚ),(5277/1955:ℚ),(-36086/13685:ℚ),(-3779/27370:ℚ),(43/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-1/3220:ℚ),(2/2737:ℚ),(33/1955:ℚ),(-8213/54740:ℚ),(5413/10948:ℚ),(-7247/13685:ℚ),(-9953/13685:ℚ),(103923/54740:ℚ),(-871/10948:ℚ),(-4461/1955:ℚ),(4874/2737:ℚ),(-24543/54740:ℚ),(-369/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-2/13685:ℚ),(2/805:ℚ),(-194/13685:ℚ),(402/13685:ℚ),(106/13685:ℚ),(-1514/13685:ℚ),(1882/13685:ℚ),(-6/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/15640:ℚ),(-87/109480:ℚ),(951/109480:ℚ),(-541/109480:ℚ),(-26939/109480:ℚ),(3797/3128:ℚ),(-42061/21896:ℚ),(-32263/15640:ℚ),(1401627/109480:ℚ),(-2073217/109480:ℚ),(542109/109480:ℚ),(2032557/109480:ℚ),(-2594681/109480:ℚ),(1277529/109480:ℚ),(-124979/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n4]
  all_goals ring
def num005 : List ℚ := [(1/109480:ℚ),(-2/13685:ℚ),(3/6440:ℚ),(333/54740:ℚ),(-3901/54740:ℚ),(9767/27370:ℚ),(-56029/54740:ℚ),(4243/2737:ℚ),(10133/109480:ℚ),(-80749/13685:ℚ),(1407599/109480:ℚ),(-139799/10948:ℚ),(21657/5474:ℚ),(19391/5474:ℚ),(-6761/1955:ℚ),(3367/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(4/13685:ℚ),(-13/27370:ℚ),(-2/119:ℚ),(7277/54740:ℚ),(-5434/13685:ℚ),(293/805:ℚ),(8796/13685:ℚ),(-14257/7820:ℚ),(20064/13685:ℚ),(23811/27370:ℚ),(-54982/13685:ℚ),(225707/54740:ℚ),(-1082/805:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(2/13685:ℚ),(-47/109480:ℚ),(-86/13685:ℚ),(333/4760:ℚ),(-411/1190:ℚ),(105517/109480:ℚ),(-430/391:ℚ),(-29909/15640:ℚ),(21215/2737:ℚ),(-710253/109480:ℚ),(-17580/2737:ℚ),(1743913/109480:ℚ),(-329813/27370:ℚ),(264239/109480:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(1/3910:ℚ),(-4/13685:ℚ),(-202/13685:ℚ),(3211/27370:ℚ),(-5123/13685:ℚ),(674/1955:ℚ),(3175/2737:ℚ),(-12461/3220:ℚ),(14271/3910:ℚ),(972/391:ℚ),(-119993/13685:ℚ),(103212/13685:ℚ),(-4443/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(-1/13685:ℚ),(467/27370:ℚ),(-5303/54740:ℚ),(452/2737:ℚ),(923/13685:ℚ),(166/13685:ℚ),(-16589/10948:ℚ),(35367/27370:ℚ),(38106/13685:ℚ),(-3309/782:ℚ),(1355/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-11/54740:ℚ),(9/3910:ℚ),(38/13685:ℚ),(-2129/13685:ℚ),(9621/10948:ℚ),(-4903/2737:ℚ),(-6122/13685:ℚ),(19804/2737:ℚ),(-514313/54740:ℚ),(56111/27370:ℚ),(45772/13685:ℚ),(-6819/2737:ℚ),(-3363/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n10]
  all_goals ring
def num011 : List ℚ := [(-1/54740:ℚ),(1/3910:ℚ),(-11/27370:ℚ),(-359/27370:ℚ),(93/805:ℚ),(-2571/5474:ℚ),(14477/13685:ℚ),(-13978/13685:ℚ),(-70537/54740:ℚ),(165819/27370:ℚ),(-276819/27370:ℚ),(269147/27370:ℚ),(-21671/3910:ℚ),(5411/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.n11]
  all_goals ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even054.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even054.den,Blueprint.Thomson.Finite.RFCatalogue.rf1325]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even054.PairData
