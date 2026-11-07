import AllS.Units.N_FI.N_kernels.RFColumns.Even074_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even074.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/54740:ℚ),(37/109480:ℚ),(-33/21896:ℚ),(-1313/109480:ℚ),(4793/27370:ℚ),(-103237/109480:ℚ),(44281/15640:ℚ),(-111075/21896:ℚ),(148881/27370:ℚ),(-25693/6440:ℚ),(60623/15640:ℚ),(-481991/109480:ℚ),(82479/27370:ℚ),(-236563/109480:ℚ),(-517/920:ℚ),(362167/109480:ℚ),(9795/10948:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/218960:ℚ),(1/13685:ℚ),(-3/13685:ℚ),(-181/54740:ℚ),(8019/218960:ℚ),(-79/476:ℚ),(5044/13685:ℚ),(-563/3220:ℚ),(-46871/43792:ℚ),(64951/27370:ℚ),(-30789/27370:ℚ),(-60863/54740:ℚ),(-332391/218960:ℚ),(333651/54740:ℚ),(-20389/5474:ℚ),(-64881/54740:ℚ),(41/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-3/7820:ℚ),(57/27370:ℚ),(164/13685:ℚ),(-5779/27370:ℚ),(65043/54740:ℚ),(-1187/340:ℚ),(72784/13685:ℚ),(-134187/54740:ℚ),(-40875/10948:ℚ),(10903/2737:ℚ),(14036/13685:ℚ),(-384/13685:ℚ),(-115911/54740:ℚ),(-447/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(33/54740:ℚ),(66/13685:ℚ),(-81/3910:ℚ),(-281/13685:ℚ),(5293/27370:ℚ),(-66/391:ℚ),(-19699/54740:ℚ),(17601/27370:ℚ),(-25/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-9/27370:ℚ),(37/27370:ℚ),(3/238:ℚ),(-809/4760:ℚ),(23853/27370:ℚ),(-131847/54740:ℚ),(93287/27370:ℚ),(-17557/21896:ℚ),(-115911/27370:ℚ),(30542/13685:ℚ),(305103/27370:ℚ),(-2396777/109480:ℚ),(470627/27370:ℚ),(-361803/54740:ℚ),(2439/3910:ℚ),(66131/21896:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n4]
  all_goals ring
def num005 : List ℚ := [(1/218960:ℚ),(-1/13685:ℚ),(13/54740:ℚ),(167/54740:ℚ),(-7943/218960:ℚ),(9869/54740:ℚ),(-26793/54740:ℚ),(33293/54740:ℚ),(91543/218960:ℚ),(-73999/27370:ℚ),(40237/10948:ℚ),(-17023/10948:ℚ),(296347/218960:ℚ),(-87063/10948:ℚ),(759923/54740:ℚ),(-32801/3220:ℚ),(4383/1564:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(1/2737:ℚ),(-19/10948:ℚ),(-183/13685:ℚ),(538/2737:ℚ),(-27621/27370:ℚ),(73091/27370:ℚ),(-1324/391:ℚ),(12983/54740:ℚ),(58334/13685:ℚ),(-172371/54740:ℚ),(-1021/2737:ℚ),(-51007/27370:ℚ),(102007/27370:ℚ),(-209/161:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(19/109480:ℚ),(-93/109480:ℚ),(-569/109480:ℚ),(113/1288:ℚ),(-58087/109480:ℚ),(209037/109480:ℚ),(-69281/15640:ℚ),(675489/109480:ℚ),(-335331/109480:ℚ),(-543579/109480:ℚ),(1082593/109480:ℚ),(-886469/109480:ℚ),(172075/21896:ℚ),(-777781/109480:ℚ),(-2477/21896:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(1/7820:ℚ),(-3/15640:ℚ),(-93/13685:ℚ),(1597/27370:ℚ),(-263/1190:ℚ),(167/391:ℚ),(-4057/13685:ℚ),(-8941/21896:ℚ),(66407/54740:ℚ),(-36531/15640:ℚ),(11232/1955:ℚ),(-77919/7820:ℚ),(16733/1955:ℚ),(-4333/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-19/54740:ℚ),(19/13685:ℚ),(201/13685:ℚ),(-9893/54740:ℚ),(6461/7820:ℚ),(-26024/13685:ℚ),(26848/13685:ℚ),(2071/54740:ℚ),(-48941/54740:ℚ),(-31887/13685:ℚ),(62651/13685:ℚ),(-179427/54740:ℚ),(1521/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(3/13685:ℚ),(3/10948:ℚ),(-43/2737:ℚ),(929/10948:ℚ),(-86/805:ℚ),(-26227/54740:ℚ),(4602/2737:ℚ),(-6915/10948:ℚ),(-61961/13685:ℚ),(48471/7820:ℚ),(19813/13685:ℚ),(-315349/54740:ℚ),(32204/13685:ℚ),(-4127/1564:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n10]
  all_goals ring
def num011 : List ℚ := [(-1/109480:ℚ),(1/7820:ℚ),(-3/15640:ℚ),(-94/13685:ℚ),(3251/54740:ℚ),(-433/1955:ℚ),(19837/54740:ℚ),(451/2737:ℚ),(-40249/21896:ℚ),(175019/54740:ℚ),(-181521/109480:ℚ),(-32219/13685:ℚ),(67203/13685:ℚ),(-100183/27370:ℚ),(817/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.n11]
  all_goals ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even074.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even074.den,Blueprint.Thomson.Finite.RFCatalogue.rf1666]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even074.PairData
