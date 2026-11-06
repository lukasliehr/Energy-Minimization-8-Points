import AllS.Units.N_FI.N_kernels.RFColumns.Even038_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even038.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-11/27370:ℚ),(223/109480:ℚ),(283/10948:ℚ),(-1279/2737:ℚ),(189951/54740:ℚ),(-245829/15640:ℚ),(1321209/27370:ℚ),(-5746287/54740:ℚ),(2242637/13685:ℚ),(-4030419/21896:ℚ),(1682683/10948:ℚ),(-2987659/27370:ℚ),(3942531/54740:ℚ),(-450011/15640:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n0]
  all_goals ring
def num001 : List ℚ := [(-1/109480:ℚ),(9/43792:ℚ),(-381/218960:ℚ),(107/15640:ℚ),(-143/10948:ℚ),(1191/43792:ℚ),(-33819/218960:ℚ),(26109/54740:ℚ),(-16309/109480:ℚ),(-113489/43792:ℚ),(1358101/218960:ℚ),(-74843/21896:ℚ),(-232133/27370:ℚ),(3528933/218960:ℚ),(-10909/1360:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-3/109480:ℚ),(1/1955:ℚ),(-47/27370:ℚ),(-496/13685:ℚ),(8131/15640:ℚ),(-47352/13685:ℚ),(39888/2737:ℚ),(-586426/13685:ℚ),(1424033/15640:ℚ),(-1891399/13685:ℚ),(782491/5474:ℚ),(-250758/2737:ℚ),(5149/184:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n2]
  all_goals ring
def num003 : List ℚ := [(1/109480:ℚ),(-9/54740:ℚ),(47/54740:ℚ),(57/54740:ℚ),(-3481/109480:ℚ),(999/5474:ℚ),(-16431/27370:ℚ),(29369/27370:ℚ),(-31281/109480:ℚ),(-1503/476:ℚ),(420751/54740:ℚ),(-65261/7820:ℚ),(3199/920:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n3]
  all_goals ring
def num004 : List ℚ := [(-1/54740:ℚ),(3/6440:ℚ),(-43/10948:ℚ),(-11/13685:ℚ),(2993/10948:ℚ),(-275469/109480:ℚ),(687657/54740:ℚ),(-553736/13685:ℚ),(4794997/54740:ℚ),(-13649663/109480:ℚ),(5480743/54740:ℚ),(-15297/13685:ℚ),(-5524937/54740:ℚ),(2483685/21896:ℚ),(-360287/7820:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n4]
  all_goals ring
def num005 : List ℚ := [(-1/218960:ℚ),(5/43792:ℚ),(-25/21896:ℚ),(737/109480:ℚ),(-1129/31280:ℚ),(45519/218960:ℚ),(-51721/54740:ℚ),(149929/54740:ℚ),(-922631/218960:ℚ),(-6247/31280:ℚ),(247577/15640:ℚ),(-3775539/109480:ℚ),(216493/6256:ℚ),(-422513/31280:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n5]
  all_goals ring
def num006 : List ℚ := [(1/109480:ℚ),(-1/3220:ℚ),(201/54740:ℚ),(-579/54740:ℚ),(-17133/109480:ℚ),(1461/782:ℚ),(-687/70:ℚ),(171133/5474:ℚ),(-7219273/109480:ℚ),(5134627/54740:ℚ),(-947179/10948:ℚ),(148417/3220:ℚ),(-9741/920:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-1/5474:ℚ),(43/54740:ℚ),(537/54740:ℚ),(-17201/109480:ℚ),(2747/2380:ℚ),(-9241/1610:ℚ),(572743/27370:ℚ),(-6237081/109480:ℚ),(317157/2737:ℚ),(-9392553/54740:ℚ),(1363999/7820:ℚ),(-2427883/21896:ℚ),(271647/7820:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n7]
  all_goals ring
def num008 : List ℚ := [(1/109480:ℚ),(-3/15640:ℚ),(167/109480:ℚ),(-111/15640:ℚ),(939/27370:ℚ),(-9143/54740:ℚ),(28017/54740:ℚ),(-41287/54740:ℚ),(-20067/109480:ℚ),(355379/109480:ℚ),(-690841/109480:ℚ),(14701/3128:ℚ),(-8379/7820:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(1/2380:ℚ),(-27/10948:ℚ),(-923/54740:ℚ),(81/238:ℚ),(-9663/3910:ℚ),(59589/5474:ℚ),(-865679/27370:ℚ),(3310187/54740:ℚ),(-803889/10948:ℚ),(2872997/54740:ℚ),(-1613/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n9]
  all_goals ring
def num010 : List ℚ := [(3/109480:ℚ),(-3/5474:ℚ),(67/27370:ℚ),(49/1955:ℚ),(-40057/109480:ℚ),(28316/13685:ℚ),(-3831/595:ℚ),(27873/2737:ℚ),(53449/109480:ℚ),(-1000457/27370:ℚ),(2047303/27370:ℚ),(-140628/1955:ℚ),(461643/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n10]
  all_goals ring
def num011 : List ℚ := [(1/109480:ℚ),(-19/109480:ℚ),(121/109480:ℚ),(-431/109480:ℚ),(1543/54740:ℚ),(-10653/54740:ℚ),(34763/54740:ℚ),(-43693/54740:ℚ),(-69119/109480:ℚ),(87385/21896:ℚ),(-686879/109480:ℚ),(50783/15640:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even038.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even038.den,Blueprint.Thomson.Finite.RFCatalogue.rf1309]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even038.PairData
