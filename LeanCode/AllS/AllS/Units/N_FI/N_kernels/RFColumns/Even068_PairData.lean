import AllS.Units.N_FI.N_kernels.RFColumns.Even068_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even068.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(1/6440:ℚ),(-3/5474:ℚ),(-74/13685:ℚ),(6869/109480:ℚ),(-4817/15640:ℚ),(10959/10948:ℚ),(-36039/13685:ℚ),(96879/15640:ℚ),(-1314221/109480:ℚ),(8443/595:ℚ),(-11551/13685:ℚ),(-2125309/109480:ℚ),(1421011/109480:ℚ),(9413/1564:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-3/54740:ℚ),(3/3220:ℚ),(-263/54740:ℚ),(-249/54740:ℚ),(297/1955:ℚ),(-233/322:ℚ),(45557/27370:ℚ),(-35429/27370:ℚ),(-200547/54740:ℚ),(683303/54740:ℚ),(-756019/54740:ℚ),(4387/54740:ℚ),(281/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-4/13685:ℚ),(37/54740:ℚ),(183/13685:ℚ),(-1636/13685:ℚ),(6546/13685:ℚ),(-6995/5474:ℚ),(1136/391:ℚ),(-1831/340:ℚ),(74626/13685:ℚ),(23241/54740:ℚ),(-60311/13685:ℚ),(33/46:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-1/3910:ℚ),(9/10948:ℚ),(0/1:ℚ),(29/1610:ℚ),(-131/805:ℚ),(2521/5474:ℚ),(-1212/2737:ℚ),(-8383/10948:ℚ),(90053/27370:ℚ),(-317/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n3]
  all_goals ring
def num004 : List ℚ := [(1/109480:ℚ),(-9/54740:ℚ),(67/109480:ℚ),(93/13685:ℚ),(-8921/109480:ℚ),(4181/10948:ℚ),(-15193/15640:ℚ),(1122/805:ℚ),(-141417/109480:ℚ),(142257/54740:ℚ),(-57859/6440:ℚ),(33891/1955:ℚ),(-1245183/109480:ℚ),(-739233/54740:ℚ),(66389/3128:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-11/54740:ℚ),(2/13685:ℚ),(79/10948:ℚ),(-2693/54740:ℚ),(5777/27370:ℚ),(-11474/13685:ℚ),(10269/3910:ℚ),(-242617/54740:ℚ),(-1937/2380:ℚ),(261612/13685:ℚ),(-274439/7820:ℚ),(36687/1564:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(4/13685:ℚ),(-29/54740:ℚ),(-439/27370:ℚ),(3639/27370:ℚ),(-38/85:ℚ),(19087/27370:ℚ),(-361/805:ℚ),(6917/7820:ℚ),(-60034/13685:ℚ),(453183/54740:ℚ),(-153743/27370:ℚ),(4/23:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-3/21896:ℚ),(1/13685:ℚ),(503/54740:ℚ),(-6983/109480:ℚ),(15979/109480:ℚ),(439/2737:ℚ),(-2683/1610:ℚ),(473027/109480:ℚ),(-780841/109480:ℚ),(27588/2737:ℚ),(-592849/54740:ℚ),(161191/21896:ℚ),(-14481/3128:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/54740:ℚ),(-9/13685:ℚ),(47/7820:ℚ),(-228/13685:ℚ),(-1147/27370:ℚ),(318/805:ℚ),(-27367/27370:ℚ),(1060/2737:ℚ),(171477/54740:ℚ),(-70501/13685:ℚ),(1943/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(13/54740:ℚ),(19/54740:ℚ),(-141/7820:ℚ),(2521/27370:ℚ),(-2377/27370:ℚ),(-793/1190:ℚ),(71147/27370:ℚ),(-6635/1564:ℚ),(45233/10948:ℚ),(-29299/7820:ℚ),(247/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/10948:ℚ),(27/27370:ℚ),(-13/54740:ℚ),(-534/13685:ℚ),(339/1610:ℚ),(-857/1955:ℚ),(1483/5474:ℚ),(2218/13685:ℚ),(-49057/54740:ℚ),(29471/5474:ℚ),(-13131/1564:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(9/27370:ℚ),(19/27370:ℚ),(-50/2737:ℚ),(1161/13685:ℚ),(-367/1955:ℚ),(111/391:ℚ),(-5618/13685:ℚ),(-10481/27370:ℚ),(108257/27370:ℚ),(-4239/782:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even068.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even068.den,Blueprint.Thomson.Finite.RFCatalogue.rf1660]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even068.PairData
