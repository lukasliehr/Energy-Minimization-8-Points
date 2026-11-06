import AllS.Units.N_FI.N_kernels.RFColumns.Even024_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even024.PairData
def num000 : List ℚ := [(0/1:ℚ),(-9/27370:ℚ),(361/54740:ℚ),(-579/13685:ℚ),(71/10948:ℚ),(35877/27370:ℚ),(-44663/5474:ℚ),(362522/13685:ℚ),(-82701/1610:ℚ),(1344841/27370:ℚ),(167593/10948:ℚ),(-1156759/13685:ℚ),(2524231/54740:ℚ),(93773/3910:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n0]
  all_goals ring
def num001 : List ℚ := [(-2/13685:ℚ),(39/13685:ℚ),(-479/27370:ℚ),(-61/27370:ℚ),(7453/13685:ℚ),(-8206/2737:ℚ),(102513/13685:ℚ),(-81421/13685:ℚ),(-33112/1955:ℚ),(739811/13685:ℚ),(-1498747/27370:ℚ),(-10247/3910:ℚ),(2793/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n1]
  all_goals ring
def num002 : List ℚ := [(-1/13685:ℚ),(87/54740:ℚ),(-6/595:ℚ),(-53/2380:ℚ),(8528/13685:ℚ),(-4303/1190:ℚ),(30062/2737:ℚ),(-540287/27370:ℚ),(36807/1955:ℚ),(-8657/10948:ℚ),(-25796/1955:ℚ),(363/92:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n2]
  all_goals ring
def num003 : List ℚ := [(1/13685:ℚ),(-13/13685:ℚ),(3/1955:ℚ),(12/805:ℚ),(18/805:ℚ),(-1726/2737:ℚ),(330/161:ℚ),(-27588/13685:ℚ),(-45139/13685:ℚ),(180539/13685:ℚ),(-1521/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n3]
  all_goals ring
def num004 : List ℚ := [(1/27370:ℚ),(-3/3910:ℚ),(361/54740:ℚ),(-39/1955:ℚ),(-1297/10948:ℚ),(21433/13685:ℚ),(-45307/5474:ℚ),(367548/13685:ℚ),(-111844/1955:ℚ),(1969963/27370:ℚ),(-1171579/54740:ℚ),(-1283/17:ℚ),(670469/7820:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n4]
  all_goals ring
def num005 : List ℚ := [(-1/13685:ℚ),(13/5474:ℚ),(-292/13685:ℚ),(159/5474:ℚ),(8664/13685:ℚ),(-8927/1955:ℚ),(196114/13685:ℚ),(-274691/13685:ℚ),(-136567/13685:ℚ),(350471/3910:ℚ),(-287042/1955:ℚ),(361277/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n5]
  all_goals ring
def num006 : List ℚ := [(-3/54740:ℚ),(27/27370:ℚ),(-131/54740:ℚ),(-802/13685:ℚ),(15557/27370:ℚ),(-35907/13685:ℚ),(238649/27370:ℚ),(-17706/805:ℚ),(1885337/54740:ℚ),(-5739/230:ℚ),(1751/460:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n6]
  all_goals ring
def num007 : List ℚ := [(1/54740:ℚ),(1/2737:ℚ),(-709/54740:ℚ),(1443/13685:ℚ),(-957/3910:ℚ),(-11882/13685:ℚ),(191339/27370:ℚ),(-17926/805:ℚ),(2468581/54740:ℚ),(-772027/13685:ℚ),(315881/7820:ℚ),(-39611/1955:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n7]
  all_goals ring
def num008 : List ℚ := [(3/13685:ℚ),(-107/27370:ℚ),(457/27370:ℚ),(1016/13685:ℚ),(-11986/13685:ℚ),(40729/13685:ℚ),(-52083/13685:ℚ),(-48644/13685:ℚ),(38829/1955:ℚ),(-18949/782:ℚ),(22099/3910:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n8]
  all_goals ring
def num009 : List ℚ := [(3/27370:ℚ),(-67/27370:ℚ),(8/391:ℚ),(-20/391:ℚ),(-5417/13685:ℚ),(50357/13685:ℚ),(-34380/2737:ℚ),(294736/13685:ℚ),(-75151/3910:ℚ),(363/46:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(19/27370:ℚ),(-87/7820:ℚ),(886/13685:ℚ),(-169/27370:ℚ),(-2549/1955:ℚ),(26391/5474:ℚ),(-76066/13685:ℚ),(-46859/7820:ℚ),(115261/3910:ℚ),(-268723/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n10]
  all_goals ring
def num011 : List ℚ := [(2/13685:ℚ),(-7/1955:ℚ),(258/13685:ℚ),(978/13685:ℚ),(-13114/13685:ℚ),(1256/391:ℚ),(-49594/13685:ℚ),(-3874/805:ℚ),(8400/391:ℚ),(-45297/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even024.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even024.den,Blueprint.Thomson.Finite.RFCatalogue.rf1055]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even024.PairData
