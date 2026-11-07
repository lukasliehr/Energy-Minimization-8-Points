import AllS.Units.N_FI.N_kernels.RFColumns.Even071_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even071.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-1/5474:ℚ),(3/3128:ℚ),(9/1610:ℚ),(-10687/109480:ℚ),(30609/54740:ℚ),(-189787/109480:ℚ),(4775/1564:ℚ),(-286277/109480:ℚ),(-1696/13685:ℚ),(49071/21896:ℚ),(-2911/1955:ℚ),(-171357/109480:ℚ),(277177/54740:ℚ),(-69637/21896:ℚ),(-14407/10948:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/109480:ℚ),(-13/109480:ℚ),(1/109480:ℚ),(171/21896:ℚ),(-2997/54740:ℚ),(1655/10948:ℚ),(-4007/54740:ℚ),(-29289/54740:ℚ),(114029/109480:ℚ),(-957/21896:ℚ),(-103251/109480:ℚ),(-100389/109480:ℚ),(45159/27370:ℚ),(1287/805:ℚ),(-32/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-9/13685:ℚ),(129/54740:ℚ),(767/27370:ℚ),(-17729/54740:ℚ),(19904/13685:ℚ),(-18259/5474:ℚ),(45229/13685:ℚ),(12774/13685:ℚ),(-52459/13685:ℚ),(-7/68:ℚ),(69903/27370:ℚ),(-53/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-4/13685:ℚ),(67/54740:ℚ),(32/13685:ℚ),(-947/27370:ℚ),(264/1955:ℚ),(-8213/27370:ℚ),(2336/13685:ℚ),(53749/54740:ℚ),(-5860/2737:ℚ),(109/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n3]
  all_goals ring
def num004 : List ℚ := [(-1/109480:ℚ),(19/109480:ℚ),(-89/109480:ℚ),(-653/109480:ℚ),(9997/109480:ℚ),(-54769/109480:ℚ),(163157/109480:ℚ),(-52225/21896:ℚ),(121361/109480:ℚ),(293977/109480:ℚ),(-478759/109480:ℚ),(123377/109480:ℚ),(165027/109480:ℚ),(-160603/109480:ℚ),(25531/6440:ℚ),(-97203/21896:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n4]
  all_goals ring
def num005 : List ℚ := [(-1/109480:ℚ),(13/109480:ℚ),(-1/15640:ℚ),(-771/109480:ℚ),(719/13685:ℚ),(-107/644:ℚ),(9663/54740:ℚ),(22269/54740:ℚ),(-164049/109480:ℚ),(24685/21896:ℚ),(13981/6440:ℚ),(-417591/109480:ℚ),(-117571/54740:ℚ),(3340/391:ℚ),(-3787/782:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(9/27370:ℚ),(-67/54740:ℚ),(-369/27370:ℚ),(905/5474:ℚ),(-93/115:ℚ),(59261/27370:ℚ),(-8277/2737:ℚ),(8197/7820:ℚ),(14073/5474:ℚ),(-33115/10948:ℚ),(263/322:ℚ),(17/161:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-9/54740:ℚ),(13/21896:ℚ),(383/54740:ℚ),(-8907/109480:ℚ),(1467/3910:ℚ),(-15401/15640:ℚ),(2081/1190:ℚ),(-280829/109480:ℚ),(142731/54740:ℚ),(9419/6440:ℚ),(-473997/54740:ℚ),(944103/109480:ℚ),(-37607/13685:ℚ),(30887/21896:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-11/54740:ℚ),(-1/3220:ℚ),(11/805:ℚ),(-173/2380:ℚ),(3169/27370:ℚ),(7419/27370:ℚ),(-2676/1955:ℚ),(111/68:ℚ),(75553/54740:ℚ),(-41947/7820:ℚ),(541/115:ℚ),(-2051/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(9/27370:ℚ),(-3/2737:ℚ),(-209/13685:ℚ),(9053/54740:ℚ),(-9461/13685:ℚ),(18918/13685:ℚ),(-10936/13685:ℚ),(-14137/7820:ℚ),(84281/27370:ℚ),(-1691/13685:ℚ),(-5127/2737:ℚ),(55/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n9]
  all_goals ring
def num010 : List ℚ := [(1/54740:ℚ),(-4/13685:ℚ),(1/1610:ℚ),(869/54740:ℚ),(-7711/54740:ℚ),(26177/54740:ℚ),(-7073/13685:ℚ),(-30063/27370:ℚ),(198403/54740:ℚ),(-4119/1610:ℚ),(-2343/1610:ℚ),(42649/54740:ℚ),(53931/54740:ℚ),(1695/1564:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n10]
  all_goals ring
def num011 : List ℚ := [(1/54740:ℚ),(-11/54740:ℚ),(-4/13685:ℚ),(37/2737:ℚ),(-1038/13685:ℚ),(4609/27370:ℚ),(-36/805:ℚ),(-6096/13685:ℚ),(30561/54740:ℚ),(4129/54740:ℚ),(11398/13685:ℚ),(-8803/2737:ℚ),(1669/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.n11]
  all_goals ring
def denominator : List ℚ := [(1/13685:ℚ),(-12/13685:ℚ),(-24/13685:ℚ),(852/13685:ℚ),(-774/2737:ℚ),(4476/13685:ℚ),(9024/13685:ℚ),(-24132/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even071.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even071.den,Blueprint.Thomson.Finite.RFCatalogue.rf1663]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even071.PairData
