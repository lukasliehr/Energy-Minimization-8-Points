import AllS.Units.N_FI.N_kernels.RFColumns.Even023_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even023.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/10948:ℚ),(5/2737:ℚ),(-673/54740:ℚ),(209/13685:ℚ),(3352/13685:ℚ),(-3466/1955:ℚ),(25681/3910:ℚ),(-42222/2737:ℚ),(232111/10948:ℚ),(-137859/13685:ℚ),(-555997/54740:ℚ),(92549/13685:ℚ),(6167/782:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n0]
  all_goals ring
def num001 : List ℚ := [(-1/27370:ℚ),(41/54740:ℚ),(-293/54740:ℚ),(509/54740:ℚ),(4959/54740:ℚ),(-18471/27370:ℚ),(55803/27370:ℚ),(-66071/27370:ℚ),(-41183/13685:ℚ),(157441/10948:ℚ),(-964641/54740:ℚ),(151889/54740:ℚ),(515/68:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n1]
  all_goals ring
def num002 : List ℚ := [(-1/54740:ℚ),(11/27370:ℚ),(-21/7820:ℚ),(-81/27370:ℚ),(3709/27370:ℚ),(-1644/1955:ℚ),(15531/5474:ℚ),(-84992/13685:ℚ),(93915/10948:ℚ),(-22349/3910:ℚ),(1443/2380:ℚ),(-13/46:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n2]
  all_goals ring
def num003 : List ℚ := [(1/54740:ℚ),(-1/3910:ℚ),(9/10948:ℚ),(0/1:ℚ),(29/1610:ℚ),(-131/805:ℚ),(2521/5474:ℚ),(-1212/2737:ℚ),(-8383/10948:ℚ),(90053/27370:ℚ),(-317/92:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n3]
  all_goals ring
def num004 : List ℚ := [(1/54740:ℚ),(-1/2737:ℚ),(27/10948:ℚ),(-11/27370:ℚ),(-260/2737:ℚ),(9552/13685:ℚ),(-78573/27370:ℚ),(16021/1955:ℚ),(-926503/54740:ℚ),(308633/13685:ℚ),(-578957/54740:ℚ),(-463843/27370:ℚ),(17753/782:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n4]
  all_goals ring
def num005 : List ℚ := [(-1/54740:ℚ),(1/1610:ℚ),(-327/54740:ℚ),(198/13685:ℚ),(3107/27370:ℚ),(-13683/13685:ℚ),(94489/27370:ℚ),(-74804/13685:ℚ),(-66197/54740:ℚ),(84763/3910:ℚ),(-295373/7820:ℚ),(9534/391:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n5]
  all_goals ring
def num006 : List ℚ := [(-1/54740:ℚ),(9/27370:ℚ),(-9/10948:ℚ),(-262/13685:ℚ),(5167/27370:ℚ),(-12209/13685:ℚ),(11801/3910:ℚ),(-103518/13685:ℚ),(631523/54740:ℚ),(-12783/1610:ℚ),(85/92:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(11/54740:ℚ),(-57/13685:ℚ),(93/3220:ℚ),(-716/13685:ℚ),(-1709/5474:ℚ),(30082/13685:ℚ),(-11579/1610:ℚ),(208868/13685:ℚ),(-12693/644:ℚ),(195359/13685:ℚ),(-10541/1564:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n7]
  all_goals ring
def num008 : List ℚ := [(3/54740:ℚ),(-2/1955:ℚ),(291/54740:ℚ),(16/1955:ℚ),(-4937/27370:ℚ),(9776/13685:ℚ),(-30517/27370:ℚ),(-7256/13685:ℚ),(15999/3220:ℚ),(-2558/391:ℚ),(2541/1564:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n8]
  all_goals ring
def num009 : List ℚ := [(1/27370:ℚ),(-1/1190:ℚ),(96/13685:ℚ),(-208/13685:ℚ),(-423/2737:ℚ),(17669/13685:ℚ),(-11468/2737:ℚ),(95988/13685:ℚ),(-35239/5474:ℚ),(135/46:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n9]
  all_goals ring
def num010 : List ℚ := [(-1/54740:ℚ),(11/27370:ℚ),(-193/54740:ℚ),(122/13685:ℚ),(241/3910:ℚ),(-6703/13685:ℚ),(34499/27370:ℚ),(-13798/13685:ℚ),(-113293/54740:ℚ),(222507/27370:ℚ),(-15063/1564:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n10]
  all_goals ring
def num011 : List ℚ := [(1/27370:ℚ),(-13/13685:ℚ),(78/13685:ℚ),(142/13685:ℚ),(-127/595:ℚ),(10656/13685:ℚ),(-13626/13685:ℚ),(-2654/2737:ℚ),(145833/27370:ℚ),(-2361/391:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even023.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even023.den,Blueprint.Thomson.Finite.RFCatalogue.rf1054]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even023.PairData
