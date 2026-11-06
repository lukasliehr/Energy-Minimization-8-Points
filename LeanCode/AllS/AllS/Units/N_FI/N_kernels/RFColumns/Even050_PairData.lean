import AllS.Units.N_FI.N_kernels.RFColumns.Even050_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even050.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/109480:ℚ),(2/13685:ℚ),(-1/3910:ℚ),(-13/1564:ℚ),(7611/109480:ℚ),(-107/460:ℚ),(3952/13685:ℚ),(1767/3910:ℚ),(-280603/109480:ℚ),(134739/27370:ℚ),(-18645/5474:ℚ),(-167947/54740:ℚ),(446881/109480:ℚ),(73023/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(19/13685:ℚ),(-22/2737:ℚ),(-1/805:ℚ),(2528/13685:ℚ),(-549/805:ℚ),(7368/13685:ℚ),(26737/13685:ℚ),(-58083/13685:ℚ),(2746/2737:ℚ),(202/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/10948:ℚ),(11/54740:ℚ),(953/54740:ℚ),(-3329/27370:ℚ),(7947/27370:ℚ),(2997/27370:ℚ),(-48681/27370:ℚ),(148993/54740:ℚ),(-12471/54740:ℚ),(-91253/54740:ℚ),(37/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-1/1955:ℚ),(19/13685:ℚ),(61/13685:ℚ),(52/13685:ℚ),(-2197/13685:ℚ),(3469/13685:ℚ),(6751/13685:ℚ),(-223/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n3]
  all_goals ring
def num004 : List ℚ := [(1/109480:ℚ),(-1/6440:ℚ),(11/27370:ℚ),(433/54740:ℚ),(-8203/109480:ℚ),(31053/109480:ℚ),(-6948/13685:ℚ),(233/1190:ℚ),(3785/3128:ℚ),(-440119/109480:ℚ),(41865/5474:ℚ),(-18457/2380:ℚ),(5369/15640:ℚ),(546139/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-1/27370:ℚ),(3/2737:ℚ),(-25/2737:ℚ),(144/13685:ℚ),(412/1955:ℚ),(-14968/13685:ℚ),(22993/13685:ℚ),(2988/1955:ℚ),(-1737/230:ℚ),(13139/1955:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(4/13685:ℚ),(-27/54740:ℚ),(-228/13685:ℚ),(3677/27370:ℚ),(-7/17:ℚ),(9967/27370:ℚ),(13569/13685:ℚ),(-24383/7820:ℚ),(47347/13685:ℚ),(-10853/7820:ℚ),(-193/805:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n6]
  all_goals ring
def num007 : List ℚ := [(1/109480:ℚ),(-2/13685:ℚ),(3/10948:ℚ),(22/2737:ℚ),(-7421/109480:ℚ),(3012/13685:ℚ),(-173/782:ℚ),(-5856/13685:ℚ),(1227/1288:ℚ),(4678/13685:ℚ),(-63569/54740:ℚ),(-222/2737:ℚ),(-58699/109480:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(3/27370:ℚ),(-5/2737:ℚ),(18/2737:ℚ),(457/13685:ℚ),(-701/2737:ℚ),(4889/13685:ℚ),(102/161:ℚ),(-3023/1955:ℚ),(1561/3910:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n8]
  all_goals ring
def num009 : List ℚ := [(-1/54740:ℚ),(1/3910:ℚ),(-3/54740:ℚ),(-31/1955:ℚ),(123/1190:ℚ),(-702/2737:ℚ),(2383/27370:ℚ),(11337/13685:ℚ),(-9599/7820:ℚ),(-19451/27370:ℚ),(1201/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(4/13685:ℚ),(-19/54740:ℚ),(-248/13685:ℚ),(3407/27370:ℚ),(-3396/13685:ℚ),(-5879/27370:ℚ),(14464/13685:ℚ),(-2441/10948:ℚ),(-3208/13685:ℚ),(-13017/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(13/27370:ℚ),(1/1955:ℚ),(-4/119:ℚ),(492/2737:ℚ),(-163/595:ℚ),(-6059/13685:ℚ),(21956/13685:ℚ),(-3235/5474:ℚ),(-4661/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even050.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even050.den,Blueprint.Thomson.Finite.RFCatalogue.rf1321]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even050.PairData
