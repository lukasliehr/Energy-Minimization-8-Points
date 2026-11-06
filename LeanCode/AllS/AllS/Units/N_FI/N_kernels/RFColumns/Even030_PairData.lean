import AllS.Units.N_FI.N_kernels.RFColumns.Even030_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even030.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/54740:ℚ),(1/27370:ℚ),(209/54740:ℚ),(-923/27370:ℚ),(1459/27370:ℚ),(5863/13685:ℚ),(-3279/1610:ℚ),(39243/13685:ℚ),(3549/7820:ℚ),(-16793/3910:ℚ),(3359/1564:ℚ),(29669/27370:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/13685:ℚ),(19/13685:ℚ),(-22/2737:ℚ),(-1/805:ℚ),(2528/13685:ℚ),(-549/805:ℚ),(7368/13685:ℚ),(26737/13685:ℚ),(-58083/13685:ℚ),(2746/2737:ℚ),(202/85:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-3/13685:ℚ),(-13/54740:ℚ),(33/2737:ℚ),(-1489/27370:ℚ),(1543/13685:ℚ),(-1141/3910:ℚ),(11343/13685:ℚ),(-47391/54740:ℚ),(-584/1955:ℚ),(359/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/27370:ℚ),(-1/1955:ℚ),(19/13685:ℚ),(61/13685:ℚ),(52/13685:ℚ),(-2197/13685:ℚ),(3469/13685:ℚ),(6751/13685:ℚ),(-223/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(3/54740:ℚ),(-2/2737:ℚ),(3/2380:ℚ),(8/391:ℚ),(-3501/27370:ℚ),(5816/13685:ℚ),(-35983/27370:ℚ),(37712/13685:ℚ),(-85977/54740:ℚ),(-46934/13685:ℚ),(238857/54740:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/27370:ℚ),(3/2737:ℚ),(-25/2737:ℚ),(144/13685:ℚ),(412/1955:ℚ),(-14968/13685:ℚ),(22993/13685:ℚ),(2988/1955:ℚ),(-1737/230:ℚ),(13139/1955:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(3/13685:ℚ),(5/10948:ℚ),(-216/13685:ℚ),(1931/27370:ℚ),(-202/2737:ℚ),(-4343/27370:ℚ),(1856/13685:ℚ),(51899/54740:ℚ),(-25209/13685:ℚ),(3253/3220:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n6]
  all_goals ring
def num007 : List ℚ := [(1/54740:ℚ),(-1/3910:ℚ),(3/54740:ℚ),(19/1190:ℚ),(-2963/27370:ℚ),(4383/13685:ℚ),(-319/782:ℚ),(-6173/13685:ℚ),(1077/340:ℚ),(-154871/27370:ℚ),(192007/54740:ℚ),(-4411/27370:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(8/13685:ℚ),(-19/13685:ℚ),(-348/13685:ℚ),(2818/13685:ℚ),(-7678/13685:ℚ),(523/2737:ℚ),(25248/13685:ℚ),(-80139/27370:ℚ),(1758/1955:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n8]
  all_goals ring
def num009 : List ℚ := [(-1/27370:ℚ),(13/27370:ℚ),(8/13685:ℚ),(-468/13685:ℚ),(2439/13685:ℚ),(-683/2737:ℚ),(-7284/13685:ℚ),(26304/13685:ℚ),(-44469/27370:ℚ),(37/322:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n9]
  all_goals ring
def num010 : List ℚ := [(1/54740:ℚ),(-3/13685:ℚ),(-33/54740:ℚ),(48/2737:ℚ),(-273/3910:ℚ),(-26/2737:ℚ),(14747/27370:ℚ),(-288/391:ℚ),(-37411/54740:ℚ),(3683/1955:ℚ),(-9107/7820:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/13685:ℚ),(-22/13685:ℚ),(99/13685:ℚ),(424/13685:ℚ),(-757/2737:ℚ),(5378/13685:ℚ),(10821/13685:ℚ),(-3308/1955:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even030.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even030.den,Blueprint.Thomson.Finite.RFCatalogue.rf1061]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even030.PairData
