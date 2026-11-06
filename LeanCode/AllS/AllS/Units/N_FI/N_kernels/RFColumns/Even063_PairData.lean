import AllS.Units.N_FI.N_kernels.RFColumns.Even063_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even063.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(9/21896:ℚ),(-79/27370:ℚ),(-157/27370:ℚ),(12991/54740:ℚ),(-42355/21896:ℚ),(24800/2737:ℚ),(-384397/13685:ℚ),(3303553/54740:ℚ),(-10043241/109480:ℚ),(159503/1610:ℚ),(-56347/782:ℚ),(1398849/54740:ℚ),(747419/109480:ℚ),(-131352/13685:ℚ),(8048/1955:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-3/218960:ℚ),(11/43792:ℚ),(-89/54740:ℚ),(1/280:ℚ),(699/218960:ℚ),(-33/31280:ℚ),(-20613/109480:ℚ),(8511/10948:ℚ),(-229413/218960:ℚ),(-2851/2576:ℚ),(23641/3910:ℚ),(-884733/109480:ℚ),(25545/43792:ℚ),(1908047/218960:ℚ),(-3877/680:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-43/109480:ℚ),(137/54740:ℚ),(79/10948:ℚ),(-6023/27370:ℚ),(191599/109480:ℚ),(-228387/27370:ℚ),(726333/27370:ℚ),(-3104147/54740:ℚ),(1223253/15640:ℚ),(-3380099/54740:ℚ),(177263/10948:ℚ),(166776/13685:ℚ),(-1613/184:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-9/54740:ℚ),(47/54740:ℚ),(57/54740:ℚ),(-3481/109480:ℚ),(999/5474:ℚ),(-16431/27370:ℚ),(29369/27370:ℚ),(-31281/109480:ℚ),(-1503/476:ℚ),(420751/54740:ℚ),(-65261/7820:ℚ),(3199/920:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n3]
  all_goals ring
def num004 : List ℚ := [(1/54740:ℚ),(-9/21896:ℚ),(321/109480:ℚ),(93/21896:ℚ),(-2936/13685:ℚ),(189401/109480:ℚ),(-865377/109480:ℚ),(16083/680:ℚ),(-2600191/54740:ℚ),(289027/4760:ℚ),(-835813/21896:ℚ),(-1321737/109480:ℚ),(239707/5474:ℚ),(-816381/21896:ℚ),(2019897/109480:ℚ),(-53229/15640:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n4]
  all_goals ring
def num005 : List ℚ := [(1/218960:ℚ),(-11/218960:ℚ),(1/54740:ℚ),(31/15640:ℚ),(-449/43792:ℚ),(159/43792:ℚ),(4365/21896:ℚ),(-66327/54740:ℚ),(831743/218960:ℚ),(-1348573/218960:ℚ),(1807/5474:ℚ),(2279253/109480:ℚ),(-575691/12880:ℚ),(9518797/218960:ℚ),(-258809/15640:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(41/109480:ℚ),(-6/2737:ℚ),(-99/13685:ℚ),(1407/7820:ℚ),(-4053/3128:ℚ),(78654/13685:ℚ),(-239583/13685:ℚ),(2008961/54740:ℚ),(-5551253/109480:ℚ),(565508/13685:ℚ),(-169886/13685:ℚ),(-393097/54740:ℚ),(4749/920:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(1/21896:ℚ),(-3/3220:ℚ),(9/1955:ℚ),(929/27370:ℚ),(-60603/109480:ℚ),(185469/54740:ℚ),(-34900/2737:ℚ),(460106/13685:ℚ),(-7130169/109480:ℚ),(1000775/10948:ℚ),(-1163383/13685:ℚ),(1120251/27370:ℚ),(3551/6440:ℚ),(-64843/7820:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-13/109480:ℚ),(9/4760:ℚ),(-281/21896:ℚ),(1215/21896:ℚ),(-10063/54740:ℚ),(1389/3220:ℚ),(-28683/54740:ℚ),(-20259/54740:ℚ),(337531/109480:ℚ),(-628121/109480:ℚ),(62053/15640:ℚ),(-11123/15640:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-1/7820:ℚ),(131/54740:ℚ),(-501/54740:ℚ),(-5903/54740:ℚ),(7365/5474:ℚ),(-36909/5474:ℚ),(528351/27370:ℚ),(-931319/27370:ℚ),(399457/10948:ℚ),(-1137201/54740:ℚ),(106919/54740:ℚ),(319/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(41/109480:ℚ),(-1/476:ℚ),(-123/10948:ℚ),(5989/27370:ℚ),(-144309/109480:ℚ),(110591/27370:ℚ),(-30087/5474:ℚ),(-183849/54740:ℚ),(2751687/109480:ℚ),(-2183627/54740:ℚ),(44831/1564:ℚ),(-13224/1955:ℚ),(-47117/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n10]
  all_goals ring
def num011 : List ℚ := [(-1/109480:ℚ),(9/109480:ℚ),(3/15640:ℚ),(-507/109480:ℚ),(236/13685:ℚ),(89/7820:ℚ),(-2151/7820:ℚ),(47367/54740:ℚ),(-107837/109480:ℚ),(-86967/109480:ℚ),(99929/21896:ℚ),(-767043/109480:ℚ),(28209/7820:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even063.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even063.den,Blueprint.Thomson.Finite.RFCatalogue.rf1655]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even063.PairData
