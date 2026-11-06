import AllS.Units.N_FI.N_kernels.RFColumns.Even060_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even060.PairData
def num000 : List ℚ := [(0/1:ℚ),(-19/109480:ℚ),(79/21896:ℚ),(-356/13685:ℚ),(2349/54740:ℚ),(60883/109480:ℚ),(-570371/109480:ℚ),(1412731/54740:ℚ),(-2332061/27370:ℚ),(20273891/109480:ℚ),(-1522123/6440:ℚ),(2579713/27370:ℚ),(10577709/54740:ℚ),(-1446549/4760:ℚ),(10900147/109480:ℚ),(750615/10948:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n0]
  all_goals ring
def num001 : List ℚ := [(-1/13685:ℚ),(41/27370:ℚ),(-148/13685:ℚ),(267/13685:ℚ),(2918/13685:ℚ),(-53877/27370:ℚ),(119072/13685:ℚ),(-309352/13685:ℚ),(367653/13685:ℚ),(776523/27370:ℚ),(-2213674/13685:ℚ),(199733/805:ℚ),(-263862/1955:ℚ),(-355395/5474:ℚ),(1654/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n1]
  all_goals ring
def num002 : List ℚ := [(-1/27370:ℚ),(7/7820:ℚ),(-403/54740:ℚ),(55/10948:ℚ),(18483/54740:ℚ),(-7844/2737:ℚ),(352841/27370:ℚ),(-1043549/27370:ℚ),(1026581/13685:ℚ),(-683673/7820:ℚ),(1994177/54740:ℚ),(2190663/54740:ℚ),(-2965317/54740:ℚ),(3643/322:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n2]
  all_goals ring
def num003 : List ℚ := [(1/27370:ℚ),(-6/13685:ℚ),(4/13685:ℚ),(86/13685:ℚ),(1859/27370:ℚ),(-11092/13685:ℚ),(46792/13685:ℚ),(-107676/13685:ℚ),(201759/27370:ℚ),(5374/391:ℚ),(-727956/13685:ℚ),(11470/161:ℚ),(-1921/46:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n3]
  all_goals ring
def num004 : List ℚ := [(3/109480:ℚ),(-31/54740:ℚ),(93/21896:ℚ),(-93/13685:ℚ),(-11817/109480:ℚ),(55897/54740:ℚ),(-614531/109480:ℚ),(334088/13685:ℚ),(-9152631/109480:ℚ),(11180579/54740:ℚ),(-34889709/109480:ℚ),(677401/2737:ℚ),(1486393/21896:ℚ),(-18356477/54740:ℚ),(5403347/21896:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n4]
  all_goals ring
def num005 : List ℚ := [(-1/27370:ℚ),(1/782:ℚ),(-179/13685:ℚ),(521/13685:ℚ),(1423/5474:ℚ),(-43/14:ℚ),(29936/1955:ℚ),(-622904/13685:ℚ),(119033/1610:ℚ),(-226187/27370:ℚ),(-147867/595:ℚ),(1547507/2737:ℚ),(-2314869/3910:ℚ),(213955/782:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n5]
  all_goals ring
def num006 : List ℚ := [(-3/54740:ℚ),(27/27370:ℚ),(-71/27370:ℚ),(-1431/27370:ℚ),(26959/54740:ℚ),(-30637/13685:ℚ),(118959/13685:ℚ),(-427883/13685:ℚ),(4458667/54740:ℚ),(-160311/1190:ℚ),(212857/1610:ℚ),(-100147/1610:ℚ),(1445/644:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n6]
  all_goals ring
def num007 : List ℚ := [(3/109480:ℚ),(-1/6440:ℚ),(-19/3220:ℚ),(879/10948:ℚ),(-2419/6440:ℚ),(46149/109480:ℚ),(96651/27370:ℚ),(-634063/27370:ℚ),(1704121/21896:ℚ),(-18312583/109480:ℚ),(2635273/10948:ℚ),(-12816973/54740:ℚ),(3136359/21896:ℚ),(-1169673/21896:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n7]
  all_goals ring
def num008 : List ℚ := [(3/27370:ℚ),(-29/13685:ℚ),(33/2737:ℚ),(164/13685:ℚ),(-33/70:ℚ),(38204/13685:ℚ),(-123392/13685:ℚ),(201622/13685:ℚ),(55737/27370:ℚ),(-109897/1955:ℚ),(284439/2737:ℚ),(-162646/1955:ℚ),(13769/782:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n8]
  all_goals ring
def num009 : List ℚ := [(1/54740:ℚ),(-41/54740:ℚ),(701/54740:ℚ),(-4989/54740:ℚ),(2301/27370:ℚ),(9173/3910:ℚ),(-392963/27370:ℚ),(163853/3910:ℚ),(-594317/7820:ℚ),(142017/1564:ℚ),(-3606487/54740:ℚ),(14411/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(1/5474:ℚ),(-78/13685:ℚ),(285/5474:ℚ),(-2031/13685:ℚ),(-5087/13685:ℚ),(50892/13685:ℚ),(-160127/13685:ℚ),(50250/2737:ℚ),(54361/27370:ℚ),(-191374/2737:ℚ),(3515597/27370:ℚ),(-37129/391:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n10]
  all_goals ring
def num011 : List ℚ := [(1/13685:ℚ),(-27/13685:ℚ),(181/13685:ℚ),(169/13685:ℚ),(-7388/13685:ℚ),(8460/2737:ℚ),(-129972/13685:ℚ),(28028/1955:ℚ),(3701/595:ℚ),(-173093/2737:ℚ),(279595/2737:ℚ),(-26631/391:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even060.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even060.den,Blueprint.Thomson.Finite.RFCatalogue.rf1652]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even060.PairData
