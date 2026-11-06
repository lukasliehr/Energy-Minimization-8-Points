import AllS.Units.N_FI.N_kernels.RFColumns.Even058_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even058.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/218960:ℚ),(13/437920:ℚ),(39/31280:ℚ),(-657/31280:ℚ),(281/2576:ℚ),(9601/31280:ℚ),(-1754603/218960:ℚ),(12751901/218960:ℚ),(-56764137/218960:ℚ),(8833137/10948:ℚ),(-3511999/1904:ℚ),(6048505/1904:ℚ),(-920766657/218960:ℚ),(961009657/218960:ℚ),(-162393349/43792:ℚ),(547987711/218960:ℚ),(-1138955/952:ℚ),(25625359/87584:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-9/875840:ℚ),(11/54740:ℚ),(-541/437920:ℚ),(-213/218960:ℚ),(24187/437920:ℚ),(-7983/21896:ℚ),(592883/437920:ℚ),(-719331/218960:ℚ),(1082807/218960:ℚ),(-9755/5474:ℚ),(-5749983/437920:ℚ),(1744881/43792:ℚ),(-763193/12512:ℚ),(5957601/109480:ℚ),(-10911031/437920:ℚ),(534307/218960:ℚ),(1545/1088:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(13/218960:ℚ),(-1/644:ℚ),(3397/218960:ℚ),(-96/1955:ℚ),(-107903/218960:ℚ),(410427/54740:ℚ),(-493057/9520:ℚ),(3187666/13685:ℚ),(-1409091/1904:ℚ),(93288513/54740:ℚ),(-623070801/218960:ℚ),(77626/23:ℚ),(-118574961/43792:ℚ),(72463577/54740:ℚ),(-773289/2576:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/218960:ℚ),(-1/15640:ℚ),(19/218960:ℚ),(121/54740:ℚ),(-355/43792:ℚ),(-4201/109480:ℚ),(79579/218960:ℚ),(-1937/1610:ℚ),(423243/218960:ℚ),(-37001/109480:ℚ),(-169833/31280:ℚ),(140229/10948:ℚ),(-28107/1840:ℚ),(1078489/109480:ℚ),(-981/368:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(3/62560:ℚ),(-151/109480:ℚ),(9/595:ℚ),(-333/6440:ℚ),(-57203/109480:ℚ),(10317/1288:ℚ),(-1483549/27370:ℚ),(1515859/6440:ℚ),(-156478093/218960:ℚ),(169486003/109480:ℚ),(-6402678/2737:ℚ),(243626049/109480:ℚ),(-11618201/15640:ℚ),(-3753967/3128:ℚ),(10953527/5474:ℚ),(-28793787/21896:ℚ),(30977641/87584:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n4]
  all_goals ring
def num005 : List ℚ := [(1/875840:ℚ),(-1/54740:ℚ),(13/87584:ℚ),(-143/218960:ℚ),(-9/3680:ℚ),(1375/21896:ℚ),(-41891/87584:ℚ),(470791/218960:ℚ),(-199763/31280:ℚ),(167684/13685:ℚ),(-4709973/437920:ℚ),(-3638737/218960:ℚ),(34490991/437920:ℚ),(-15668521/109480:ℚ),(65538691/437920:ℚ),(-2730433/31280:ℚ),(544593/25024:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(-1/31280:ℚ),(107/109480:ℚ),(-2441/218960:ℚ),(2183/54740:ℚ),(16669/43792:ℚ),(-655859/109480:ℚ),(8941559/218960:ℚ),(-4853607/27370:ℚ),(16765317/31280:ℚ),(-127010507/109480:ℚ),(394348349/218960:ℚ),(-107513033/54740:ℚ),(62665079/43792:ℚ),(-805977/1288:ℚ),(319617/2576:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-3/218960:ℚ),(109/218960:ℚ),(-295/43792:ℚ),(7397/218960:ℚ),(29713/218960:ℚ),(-693487/218960:ℚ),(5238241/218960:ℚ),(-5001083/43792:ℚ),(86234487/218960:ℚ),(-225970649/218960:ℚ),(91405739/43792:ℚ),(-30774039/9520:ℚ),(814509499/218960:ℚ),(-656690789/218960:ℚ),(331209803/218960:ℚ),(-15828361/43792:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/87584:ℚ),(-3/12880:ℚ),(583/437920:ℚ),(17/6440:ℚ),(-4269/62560:ℚ),(85083/218960:ℚ),(-544993/437920:ℚ),(3781/1564:ℚ),(-169237/87584:ℚ),(-122603/31280:ℚ),(6912317/437920:ℚ),(-80069/3128:ℚ),(9934623/437920:ℚ),(-2815/272:ℚ),(22911/12512:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(1/21896:ℚ),(-149/109480:ℚ),(831/54740:ℚ),(-397/7820:ℚ),(-11861/21896:ℚ),(123111/15640:ℚ),(-39217/782:ℚ),(324519/1610:ℚ),(-3585933/6440:ℚ),(118410333/109480:ℚ),(-80003689/54740:ℚ),(71982717/54740:ℚ),(-78021343/109480:ℚ),(229419/1288:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-1/15640:ℚ),(89/54740:ℚ),(-1569/109480:ℚ),(251/27370:ℚ),(92409/109480:ℚ),(-87489/10948:ℚ),(4210263/109480:ℚ),(-43045/391:ℚ),(3746327/21896:ℚ),(-1030529/54740:ℚ),(-60045723/109480:ℚ),(1542917/1190:ℚ),(-167842149/109480:ℚ),(10741417/10948:ℚ),(-858409/3128:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n10]
  all_goals ring
def num011 : List ℚ := [(-1/437920:ℚ),(1/31280:ℚ),(-15/87584:ℚ),(-3/15640:ℚ),(4831/437920:ℚ),(-20063/218960:ℚ),(185309/437920:ℚ),(-13775/10948:ℚ),(1014229/437920:ℚ),(-305799/218960:ℚ),(-326799/62560:ℚ),(369759/21896:ℚ),(-10529203/437920:ℚ),(3842431/218960:ℚ),(-64707/12512:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.n11]
  all_goals ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even058.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even058.den,Blueprint.Thomson.Finite.RFCatalogue.rf1650]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even058.PairData
