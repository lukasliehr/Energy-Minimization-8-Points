import AllS.Units.N_FI.N_kernels.RFColumns.Even061_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even061.PairData
def num000 : List ℚ := [(0/1:ℚ),(-19/27370:ℚ),(1549/109480:ℚ),(-1301/13685:ℚ),(656/13685:ℚ),(175379/54740:ℚ),(-2828051/109480:ℚ),(6595359/54740:ℚ),(-5215683/13685:ℚ),(10913142/13685:ℚ),(-105910793/109480:ℚ),(240183/782:ℚ),(12106427/13685:ℚ),(-807073/644:ℚ),(487059/1288:ℚ),(15141083/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n0]
  all_goals ring
def num001 : List ℚ := [(-4/13685:ℚ),(16/2737:ℚ),(-25/644:ℚ),(1079/54740:ℚ),(70543/54740:ℚ),(-541307/54740:ℚ),(79144/1955:ℚ),(-2689989/27370:ℚ),(122721/1190:ℚ),(4177389/27370:ℚ),(-39163149/54740:ℚ),(1624161/1564:ℚ),(-29097533/54740:ℚ),(-15385743/54740:ℚ),(66309/170:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n1]
  all_goals ring
def num002 : List ℚ := [(-2/13685:ℚ),(393/109480:ℚ),(-401/13685:ℚ),(589/54740:ℚ),(1167/782:ℚ),(-274945/21896:ℚ),(154680/2737:ℚ),(-4547737/27370:ℚ),(4419249/13685:ℚ),(-40818817/109480:ℚ),(2215037/13685:ℚ),(8119173/54740:ℚ),(-5757427/27370:ℚ),(58825/1288:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n2]
  all_goals ring
def num003 : List ℚ := [(2/13685:ℚ),(-1/595:ℚ),(-12/13685:ℚ),(673/13685:ℚ),(228/1955:ℚ),(-7270/2737:ℚ),(1488/119:ℚ),(-425862/13685:ℚ),(453826/13685:ℚ),(648693/13685:ℚ),(-2829972/13685:ℚ),(770305/2737:ℚ),(-18864/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n3]
  all_goals ring
def num004 : List ℚ := [(3/27370:ℚ),(-25/10948:ℚ),(267/15640:ℚ),(-1019/54740:ℚ),(-479/805:ℚ),(149761/27370:ℚ),(-3214159/109480:ℚ),(3280413/27370:ℚ),(-10455127/27370:ℚ),(48221543/54740:ℚ),(-142845153/109480:ℚ),(10056413/10948:ℚ),(5795369/13685:ℚ),(-19722079/13685:ℚ),(108947299/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n4]
  all_goals ring
def num005 : List ℚ := [(-2/13685:ℚ),(277/54740:ℚ),(-1361/27370:ℚ),(591/5474:ℚ),(5621/3910:ℚ),(-790093/54740:ℚ),(937303/13685:ℚ),(-2684331/13685:ℚ),(4149893/13685:ℚ),(175739/54740:ℚ),(-186653/170:ℚ),(65231659/27370:ℚ),(-412473/170:ℚ),(8561371/7820:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n5]
  all_goals ring
def num006 : List ℚ := [(-5/21896:ℚ),(233/54740:ℚ),(-381/27370:ℚ),(-10929/54740:ℚ),(229331/109480:ℚ),(-55911/5474:ℚ),(109810/2737:ℚ),(-44685/322:ℚ),(38420253/109480:ℚ),(-31467123/54740:ℚ),(15517401/27370:ℚ),(-886093/3220:ℚ),(120921/6440:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n6]
  all_goals ring
def num007 : List ℚ := [(13/109480:ℚ),(-3/3220:ℚ),(-31/1610:ℚ),(15789/54740:ℚ),(-147463/109480:ℚ),(14407/13685:ℚ),(232266/13685:ℚ),(-568007/5474:ℚ),(2194399/6440:ℚ),(-5631309/7820:ℚ),(800681/782:ℚ),(-10838379/10948:ℚ),(9440829/15640:ℚ),(-6033231/27370:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n7]
  all_goals ring
def num008 : List ℚ := [(6/13685:ℚ),(-453/54740:ℚ),(465/10948:ℚ),(1261/10948:ℚ),(-126169/54740:ℚ),(346639/27370:ℚ),(-1063807/27370:ℚ),(1626921/27370:ℚ),(495051/27370:ℚ),(-13459881/54740:ℚ),(673779/1564:ℚ),(-2600069/7820:ℚ),(535437/7820:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n8]
  all_goals ring
def num009 : List ℚ := [(3/54740:ℚ),(-131/54740:ℚ),(2391/54740:ℚ),(-3491/10948:ℚ),(4667/27370:ℚ),(277013/27370:ℚ),(-338001/5474:ℚ),(5029741/27370:ℚ),(-18383353/54740:ℚ),(21556121/54740:ℚ),(-2146987/7820:ℚ),(57537/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n9]
  all_goals ring
def num010 : List ℚ := [(1/109480:ℚ),(5/10948:ℚ),(-53/2737:ℚ),(10011/54740:ℚ),(-7073/15640:ℚ),(-8637/3910:ℚ),(245711/13685:ℚ),(-88317/1610:ℚ),(8725187/109480:ℚ),(326057/10948:ℚ),(-926182/2737:ℚ),(361395/644:ℚ),(-6059579/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n10]
  all_goals ring
def num011 : List ℚ := [(4/13685:ℚ),(-213/27370:ℚ),(29/595:ℚ),(2899/27370:ℚ),(-34812/13685:ℚ),(189107/13685:ℚ),(-111886/2737:ℚ),(46967/805:ℚ),(466944/13685:ℚ),(-1501181/5474:ℚ),(5816739/13685:ℚ),(-1070071/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even061.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even061.den,Blueprint.Thomson.Finite.RFCatalogue.rf1653]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even061.PairData
