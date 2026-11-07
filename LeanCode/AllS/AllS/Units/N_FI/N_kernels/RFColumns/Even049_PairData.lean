import AllS.Units.N_FI.N_kernels.RFColumns.Even049_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even049.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(3/109480:ℚ),(-29/54740:ℚ),(29/10948:ℚ),(228/13685:ℚ),(-30511/109480:ℚ),(87583/54740:ℚ),(-28039/5474:ℚ),(19466/1955:ℚ),(-37561/3128:ℚ),(526817/54740:ℚ),(-324703/54740:ℚ),(-5822/13685:ℚ),(24317/3128:ℚ),(-173379/54740:ℚ),(-7113/1955:ℚ),(-2180/2737:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/218960:ℚ),(-1/15640:ℚ),(1/10948:ℚ),(27/7820:ℚ),(-6367/218960:ℚ),(11457/109480:ℚ),(-2228/13685:ℚ),(-93/1190:ℚ),(24101/31280:ℚ),(-19387/15640:ℚ),(31659/54740:ℚ),(29041/54740:ℚ),(-31617/43792:ℚ),(55763/109480:ℚ),(-1370/2737:ℚ),(4/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/54740:ℚ),(1/2380:ℚ),(-38/13685:ℚ),(-491/54740:ℚ),(2595/10948:ℚ),(-42253/27370:ℚ),(3148/595:ℚ),(-278447/27370:ℚ),(72803/7820:ℚ),(25099/54740:ℚ),(-88838/13685:ℚ),(14713/54740:ℚ),(1801/644:ℚ),(170/161:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(33/54740:ℚ),(66/13685:ℚ),(-81/3910:ℚ),(-281/13685:ℚ),(5293/27370:ℚ),(-66/391:ℚ),(-19699/54740:ℚ),(17601/27370:ℚ),(-25/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-3/109480:ℚ),(1/1955:ℚ),(-129/54740:ℚ),(-957/54740:ℚ),(1717/6440:ℚ),(-80803/54740:ℚ),(49587/10948:ℚ),(-215731/27370:ℚ),(648199/109480:ℚ),(89979/27370:ℚ),(-89443/10948:ℚ),(-65049/54740:ℚ),(1017783/109480:ℚ),(-50751/54740:ℚ),(-265711/54740:ℚ),(-3225/2737:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n4]
  all_goals ring
def num005 : List ℚ := [(-1/218960:ℚ),(1/15640:ℚ),(-3/27370:ℚ),(-179/54740:ℚ),(6523/218960:ℚ),(-13299/109480:ℚ),(3369/13685:ℚ),(-2647/54740:ℚ),(-230859/218960:ℚ),(55925/21896:ℚ),(-24657/13685:ℚ),(-133249/54740:ℚ),(1156721/218960:ℚ),(-7535/3128:ℚ),(-4423/3910:ℚ),(1393/1564:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/7820:ℚ),(57/27370:ℚ),(93/7820:ℚ),(-1641/7820:ℚ),(32517/27370:ℚ),(-48971/13685:ℚ),(32467/5474:ℚ),(-238821/54740:ℚ),(-33353/54740:ℚ),(6337/5474:ℚ),(181623/54740:ℚ),(-194317/54740:ℚ),(113/161:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-19/54740:ℚ),(87/54740:ℚ),(164/13685:ℚ),(-1949/10948:ℚ),(53317/54740:ℚ),(-23997/7820:ℚ),(83962/13685:ℚ),(-426873/54740:ℚ),(8237/1564:ℚ),(21673/54740:ℚ),(-22942/13685:ℚ),(-3355/644:ℚ),(50017/7820:ℚ),(12527/10948:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-3/27370:ℚ),(-3/109480:ℚ),(94/13685:ℚ),(-2561/54740:ℚ),(7373/54740:ℚ),(-4391/54740:ℚ),(-1299/1955:ℚ),(234597/109480:ℚ),(-5630/2737:ℚ),(-266191/109480:ℚ),(106849/13685:ℚ),(-27303/3910:ℚ),(3395/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(19/27370:ℚ),(-11/3910:ℚ),(-79/2737:ℚ),(9887/27370:ℚ),(-23013/13685:ℚ),(54603/13685:ℚ),(-3526/805:ℚ),(2501/27370:ℚ),(841/230:ℚ),(-24641/27370:ℚ),(-1789/1955:ℚ),(-447/322:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(1/27370:ℚ),(-29/54740:ℚ),(1/1564:ℚ),(1703/54740:ℚ),(-2661/10948:ℚ),(9888/13685:ℚ),(-1647/3910:ℚ),(-73897/27370:ℚ),(140/23:ℚ),(-5069/3220:ℚ),(-383681/54740:ℚ),(231579/54740:ℚ),(69911/54740:ℚ),(1559/782:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n10]
  all_goals ring
def num011 : List ℚ := [(1/109480:ℚ),(-3/27370:ℚ),(-3/109480:ℚ),(373/54740:ℚ),(-2503/54740:ℚ),(3533/27370:ℚ),(-1075/10948:ℚ),(-9477/27370:ℚ),(12891/15640:ℚ),(-773/3910:ℚ),(-13043/21896:ℚ),(-44003/54740:ℚ),(29306/13685:ℚ),(-793/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.n11]
  all_goals ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even049.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even049.den,Blueprint.Thomson.Finite.RFCatalogue.rf1320]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even049.PairData
