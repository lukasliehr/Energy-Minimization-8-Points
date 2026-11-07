import AllS.Units.N_FI.N_kernels.RFColumns.Even064_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even064.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/21896:ℚ),(-87/54740:ℚ),(15/782:ℚ),(-9423/109480:ℚ),(25643/109480:ℚ),(-50789/54740:ℚ),(12496/2737:ℚ),(-1642429/109480:ℚ),(3239553/109480:ℚ),(-1555021/54740:ℚ),(-8503/782:ℚ),(1213935/21896:ℚ),(-3660103/109480:ℚ),(-140059/10948:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/27370:ℚ),(-19/27370:ℚ),(66/13685:ℚ),(-471/27370:ℚ),(81/1190:ℚ),(-827/1955:ℚ),(24279/13685:ℚ),(-6928/1955:ℚ),(1043/3910:ℚ),(379087/27370:ℚ),(-385653/13685:ℚ),(72409/3910:ℚ),(382059/27370:ℚ),(-409/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(1/1955:ℚ),(3/13685:ℚ),(-551/13685:ℚ),(1697/5474:ℚ),(-17427/13685:ℚ),(49821/13685:ℚ),(-4373/595:ℚ),(9777/1190:ℚ),(9704/13685:ℚ),(-205092/13685:ℚ),(205678/13685:ℚ),(-503/322:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(8/13685:ℚ),(-13/5474:ℚ),(-97/13685:ℚ),(206/1955:ℚ),(-1529/2737:ℚ),(24882/13685:ℚ),(-38867/13685:ℚ),(-29611/27370:ℚ),(23151/1955:ℚ),(-552763/27370:ℚ),(320/23:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n3]
  all_goals ring
def num004 : List ℚ := [(-1/109480:ℚ),(2/13685:ℚ),(-1/4760:ℚ),(-537/54740:ℚ),(1323/15640:ℚ),(-16019/54740:ℚ),(39611/109480:ℚ),(7087/27370:ℚ),(68529/109480:ℚ),(-60343/5474:ℚ),(559953/15640:ℚ),(-27191/476:ℚ),(3803203/109480:ℚ),(1682209/54740:ℚ),(-1095167/21896:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/3910:ℚ),(109/27370:ℚ),(-393/13685:ℚ),(2344/13685:ℚ),(-2706/2737:ℚ),(57102/13685:ℚ),(-20303/1955:ℚ),(143317/13685:ℚ),(449611/27370:ℚ),(-114137/1610:ℚ),(1382314/13685:ℚ),(-23631/391:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n5]
  all_goals ring
def num006 : List ℚ := [(1/27370:ℚ),(-29/54740:ℚ),(13/54740:ℚ),(1753/54740:ℚ),(-11139/54740:ℚ),(1889/3910:ℚ),(-33/70:ℚ),(1303/1190:ℚ),(-11103/1955:ℚ),(41999/3220:ℚ),(-139267/10948:ℚ),(32981/54740:ℚ),(3809/644:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n6]
  all_goals ring
def num007 : List ℚ := [(-3/109480:ℚ),(47/109480:ℚ),(-12/13685:ℚ),(-107/5474:ℚ),(3445/21896:ℚ),(-56657/109480:ℚ),(10769/13685:ℚ),(5484/13685:ℚ),(-662049/109480:ℚ),(2087517/109480:ℚ),(-482193/13685:ℚ),(205915/5474:ℚ),(-89987/4760:ℚ),(131105/21896:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(9/13685:ℚ),(-113/27370:ℚ),(52/2737:ℚ),(-116/805:ℚ),(11267/13685:ℚ),(-31268/13685:ℚ),(29213/13685:ℚ),(110513/27370:ℚ),(-41840/2737:ℚ),(72007/3910:ℚ),(-2079/391:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n8]
  all_goals ring
def num009 : List ℚ := [(3/54740:ℚ),(-43/54740:ℚ),(1/3220:ℚ),(2491/54740:ℚ),(-423/1610:ℚ),(10739/27370:ℚ),(5479/5474:ℚ),(-130483/27370:ℚ),(470123/54740:ℚ),(-555963/54740:ℚ),(489129/54740:ℚ),(-2817/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(3/10948:ℚ),(-1/3220:ℚ),(-739/54740:ℚ),(225/2737:ℚ),(-845/5474:ℚ),(-1237/27370:ℚ),(14561/27370:ℚ),(-72129/54740:ℚ),(165187/54740:ℚ),(-124149/54740:ℚ),(-85667/10948:ℚ),(12101/782:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(9/27370:ℚ),(-113/27370:ℚ),(407/13685:ℚ),(-2869/13685:ℚ),(2768/2737:ℚ),(-31582/13685:ℚ),(12281/13685:ℚ),(84461/13685:ℚ),(-409033/27370:ℚ),(11295/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even064.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even064.den,Blueprint.Thomson.Finite.RFCatalogue.rf1656]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even064.PairData
