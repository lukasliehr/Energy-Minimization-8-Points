import AllS.Units.N_FI.N_kernels.RFColumns.Even046_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even046.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(19/54740:ℚ),(-13/7820:ℚ),(-21/1955:ℚ),(941/5474:ℚ),(-10655/10948:ℚ),(42327/13685:ℚ),(-77872/13685:ℚ),(264643/54740:ℚ),(13241/10948:ℚ),(-11979/3220:ℚ),(-49153/13685:ℚ),(90119/13685:ℚ),(-1811/7820:ℚ),(-2615/5474:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(9/109480:ℚ),(59/109480:ℚ),(-1107/109480:ℚ),(2909/54740:ℚ),(-7081/54740:ℚ),(7683/54740:ℚ),(-359/10948:ℚ),(-24077/109480:ℚ),(154389/109480:ℚ),(-379649/109480:ℚ),(2243/952:ℚ),(10881/5474:ℚ),(-71/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-9/27370:ℚ),(3/2380:ℚ),(2/161:ℚ),(-4211/27370:ℚ),(10401/13685:ℚ),(-12051/5474:ℚ),(55934/13685:ℚ),(-261859/54740:ℚ),(15315/5474:ℚ),(18489/54740:ℚ),(-8532/13685:ℚ),(-134/161:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-4/13685:ℚ),(67/54740:ℚ),(32/13685:ℚ),(-947/27370:ℚ),(264/1955:ℚ),(-8213/27370:ℚ),(2336/13685:ℚ),(53749/54740:ℚ),(-5860/2737:ℚ),(109/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n3]
  all_goals ring
def num004 : List ℚ := [(1/54740:ℚ),(-19/54740:ℚ),(87/54740:ℚ),(19/1564:ℚ),(-579/3220:ℚ),(3789/3910:ℚ),(-158359/54740:ℚ),(26917/5474:ℚ),(-187293/54740:ℚ),(-32689/7820:ℚ),(735633/54740:ℚ),(-757899/54740:ℚ),(11401/7820:ℚ),(115917/13685:ℚ),(-38861/10948:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n4]
  all_goals ring
def num005 : List ℚ := [(1/109480:ℚ),(-11/109480:ℚ),(-3/21896:ℚ),(757/109480:ℚ),(-453/10948:ℚ),(5837/54740:ℚ),(-1115/10948:ℚ),(19/2380:ℚ),(-8039/21896:ℚ),(131993/109480:ℚ),(59837/109480:ℚ),(-34553/4760:ℚ),(44403/3910:ℚ),(-2135/391:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(9/27370:ℚ),(-9/7820:ℚ),(-393/27370:ℚ),(4479/27370:ℚ),(-1461/1955:ℚ),(51473/27370:ℚ),(-303/115:ℚ),(15599/10948:ℚ),(31053/27370:ℚ),(-10677/7820:ℚ),(-25909/27370:ℚ),(178/161:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/7820:ℚ),(4/1955:ℚ),(111/10948:ℚ),(-1969/10948:ℚ),(28111/27370:ℚ),(-9006/2737:ℚ),(4953/782:ℚ),(-367177/54740:ℚ),(98487/54740:ℚ),(58462/13685:ℚ),(-222913/54740:ℚ),(-4279/10948:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(3/13685:ℚ),(-3/13685:ℚ),(-523/54740:ℚ),(103/1610:ℚ),(-18/119:ℚ),(86/13685:ℚ),(123/238:ℚ),(-4499/7820:ℚ),(249/2737:ℚ),(-7421/13685:ℚ),(939/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(33/27370:ℚ),(-81/27370:ℚ),(-114/1955:ℚ),(7292/13685:ℚ),(-26969/13685:ℚ),(9669/2737:ℚ),(-5790/2737:ℚ),(-30431/13685:ℚ),(83961/27370:ℚ),(-53/322:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(4/13685:ℚ),(-39/54740:ℚ),(-407/27370:ℚ),(1933/13685:ℚ),(-7232/13685:ℚ),(3031/3910:ℚ),(2017/2737:ℚ),(-244617/54740:ℚ),(880/161:ℚ),(7489/10948:ℚ),(-140827/27370:ℚ),(905/782:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n10]
  all_goals ring
def num011 : List ℚ := [(-1/54740:ℚ),(9/54740:ℚ),(9/13685:ℚ),(-177/13685:ℚ),(209/3910:ℚ),(-213/3910:ℚ),(-410/2737:ℚ),(3912/13685:ℚ),(12091/54740:ℚ),(-699/3220:ℚ),(-16049/13685:ℚ),(409/391:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even046.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even046.den,Blueprint.Thomson.Finite.RFCatalogue.rf1317]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even046.PairData
