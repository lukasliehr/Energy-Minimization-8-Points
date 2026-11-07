import AllS.Units.N_FI.N_kernels.RFColumns.Even027_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even027.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/10948:ℚ),(-167/54740:ℚ),(1949/54740:ℚ),(-398/2737:ℚ),(7911/27370:ℚ),(-3073/3910:ℚ),(96253/27370:ℚ),(-428271/54740:ℚ),(8529/2380:ℚ),(587941/54740:ℚ),(-572839/54740:ℚ),(-81653/27370:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/13685:ℚ),(-19/13685:ℚ),(18/1955:ℚ),(-307/13685:ℚ),(3/2737:ℚ),(-11/2737:ℚ),(5521/13685:ℚ),(-1177/1955:ℚ),(-28316/13685:ℚ),(9938/1955:ℚ),(14333/13685:ℚ),(-594/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-3/54740:ℚ),(1/1610:ℚ),(143/54740:ℚ),(-907/13685:ℚ),(10303/27370:ℚ),(-14482/13685:ℚ),(6723/3910:ℚ),(-431/391:ℚ),(-113083/54740:ℚ),(107267/27370:ℚ),(-533/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(3/2737:ℚ),(-41/13685:ℚ),(-73/2737:ℚ),(1/5:ℚ),(-1077/1955:ℚ),(1291/1955:ℚ),(10273/13685:ℚ),(-58516/13685:ℚ),(528/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n3]
  all_goals ring
def num004 : List ℚ := [(-1/54740:ℚ),(3/10948:ℚ),(-3/13685:ℚ),(-1033/54740:ℚ),(8193/54740:ℚ),(-1879/3910:ℚ),(1390/2737:ℚ),(16211/27370:ℚ),(1657/54740:ℚ),(-24669/3220:ℚ),(4971/391:ℚ),(68163/54740:ℚ),(-690569/54740:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-8/13685:ℚ),(117/13685:ℚ),(-701/13685:ℚ),(2837/13685:ℚ),(-11149/13685:ℚ),(32751/13685:ℚ),(-1013/391:ℚ),(-15437/2737:ℚ),(53341/2737:ℚ),(-33608/1955:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n5]
  all_goals ring
def num006 : List ℚ := [(3/54740:ℚ),(-3/3910:ℚ),(1/7820:ℚ),(636/13685:ℚ),(-7873/27370:ℚ),(9523/13685:ℚ),(-539/782:ℚ),(4656/13685:ℚ),(-12129/54740:ℚ),(-4559/3910:ℚ),(6539/3220:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n6]
  all_goals ring
def num007 : List ℚ := [(-1/27370:ℚ),(1/1955:ℚ),(-13/27370:ℚ),(-326/13685:ℚ),(89/595:ℚ),(-5162/13685:ℚ),(513/1955:ℚ),(22804/13685:ℚ),(-37497/5474:ℚ),(133323/13685:ℚ),(-109729/27370:ℚ),(6666/13685:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(19/13685:ℚ),(-117/13685:ℚ),(65/2737:ℚ),(-1287/13685:ℚ),(6563/13685:ℚ),(-1971/2737:ℚ),(-20721/13685:ℚ),(7716/1955:ℚ),(-2086/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n8]
  all_goals ring
def num009 : List ℚ := [(1/13685:ℚ),(-5/5474:ℚ),(-13/13685:ℚ),(733/13685:ℚ),(-2999/13685:ℚ),(372/13685:ℚ),(4045/2737:ℚ),(-41533/13685:ℚ),(30146/13685:ℚ),(-211/322:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(1/3910:ℚ),(-9/54740:ℚ),(-142/13685:ℚ),(235/5474:ℚ),(-47/2737:ℚ),(-737/5474:ℚ),(638/1955:ℚ),(-49101/54740:ℚ),(-6649/27370:ℚ),(27189/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(13/13685:ℚ),(-29/2737:ℚ),(541/13685:ℚ),(-1401/13685:ℚ),(5839/13685:ℚ),(-9419/13685:ℚ),(-23673/13685:ℚ),(8131/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even027.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even027.den,Blueprint.Thomson.Finite.RFCatalogue.rf1058]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even027.PairData
