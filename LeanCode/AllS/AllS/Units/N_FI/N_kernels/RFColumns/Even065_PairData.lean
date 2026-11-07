import AllS.Units.N_FI.N_kernels.RFColumns.Even065_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even065.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/21896:ℚ),(-41/109480:ℚ),(-269/54740:ℚ),(988/13685:ℚ),(-37071/109480:ℚ),(20435/21896:ℚ),(-210099/54740:ℚ),(267059/13685:ℚ),(-6989081/109480:ℚ),(2640033/21896:ℚ),(-339231/3220:ℚ),(-707359/13685:ℚ),(23040419/109480:ℚ),(-113917/920:ℚ),(-2472209/54740:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(2/13685:ℚ),(-36/13685:ℚ),(417/27370:ℚ),(-13/595:ℚ),(-603/27370:ℚ),(-243/391:ℚ),(13553/2737:ℚ),(-176298/13685:ℚ),(76703/13685:ℚ),(569438/13685:ℚ),(-2555019/27370:ℚ),(802453/13685:ℚ),(18997/322:ℚ),(-7841/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-1/6440:ℚ),(25/10948:ℚ),(-73/54740:ℚ),(-1697/10948:ℚ),(140033/109480:ℚ),(-148983/27370:ℚ),(4997/322:ℚ),(-116859/3910:ℚ),(3372353/109480:ℚ),(38359/7820:ℚ),(-3139609/54740:ℚ),(19727/340:ℚ),(-10445/1288:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-2/13685:ℚ),(31/13685:ℚ),(-3/391:ℚ),(-638/13685:ℚ),(7088/13685:ℚ),(-34694/13685:ℚ),(106826/13685:ℚ),(-22432/1955:ℚ),(-17470/2737:ℚ),(710127/13685:ℚ),(-1145689/13685:ℚ),(6362/115:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n3]
  all_goals ring
def num004 : List ℚ := [(-1/21896:ℚ),(1/1288:ℚ),(-13/6440:ℚ),(-1171/27370:ℚ),(6727/15640:ℚ),(-38435/21896:ℚ),(367229/109480:ℚ),(-26802/13685:ℚ),(257077/109480:ℚ),(-3828793/109480:ℚ),(13842533/109480:ℚ),(-5759657/27370:ℚ),(2000393/15640:ℚ),(12326163/109480:ℚ),(-19920997/109480:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-5/5474:ℚ),(24/1955:ℚ),(-199/2737:ℚ),(12417/27370:ℚ),(-45363/13685:ℚ),(218682/13685:ℚ),(-16448/391:ℚ),(605431/13685:ℚ),(244353/3910:ℚ),(-759438/2737:ℚ),(1071571/2737:ℚ),(-904289/3910:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n5]
  all_goals ring
def num006 : List ℚ := [(1/6440:ℚ),(-129/54740:ℚ),(15/5474:ℚ),(1457/10948:ℚ),(-106203/109480:ℚ),(499/170:ℚ),(-13368/2737:ℚ),(43209/5474:ℚ),(-415761/21896:ℚ),(1898763/54740:ℚ),(-792187/27370:ℚ),(-429183/54740:ℚ),(153007/6440:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n6]
  all_goals ring
def num007 : List ℚ := [(-3/27370:ℚ),(19/10948:ℚ),(-9/2380:ℚ),(-871/10948:ℚ),(37297/54740:ℚ),(-67843/27370:ℚ),(124317/27370:ℚ),(1101/27370:ℚ),(-375897/13685:ℚ),(4855267/54740:ℚ),(-1702271/10948:ℚ),(4307/28:ℚ),(-515921/7820:ℚ),(206389/13685:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-2/13685:ℚ),(33/13685:ℚ),(-149/13685:ℚ),(307/13685:ℚ),(-4668/13685:ℚ),(5546/1955:ℚ),(-1070/119:ℚ),(25546/2737:ℚ),(27818/1955:ℚ),(-781511/13685:ℚ),(26941/391:ℚ),(-38899/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n8]
  all_goals ring
def num009 : List ℚ := [(3/13685:ℚ),(-173/54740:ℚ),(4/2737:ℚ),(2033/10948:ℚ),(-15458/13685:ℚ),(56663/27370:ℚ),(38576/13685:ℚ),(-532579/27370:ℚ),(554951/13685:ℚ),(-379591/7820:ℚ),(13852/391:ℚ),(-8835/644:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n9]
  all_goals ring
def num010 : List ℚ := [(-1/15640:ℚ),(53/54740:ℚ),(-31/27370:ℚ),(-533/10948:ℚ),(33877/109480:ℚ),(-517/782:ℚ),(134/2737:ℚ),(66239/27370:ℚ),(-148201/21896:ℚ),(585657/54740:ℚ),(-779/230:ℚ),(-9861/340:ℚ),(834057/15640:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/782:ℚ),(-353/27370:ℚ),(926/13685:ℚ),(-1094/1955:ℚ),(47013/13685:ℚ),(-17873/1955:ℚ),(10202/1955:ℚ),(60342/2737:ℚ),(-221059/3910:ℚ),(213633/3910:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even065.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even065.den,Blueprint.Thomson.Finite.RFCatalogue.rf1657]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even065.PairData
