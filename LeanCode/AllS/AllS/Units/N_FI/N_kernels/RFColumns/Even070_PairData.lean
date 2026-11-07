import AllS.Units.N_FI.N_kernels.RFColumns.Even070_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even070.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/119:ℚ),(5/34:ℚ),(-257/238:ℚ),(648/119:ℚ),(-2592/119:ℚ),(7349/119:ℚ),(-1957/17:ℚ),(13954/119:ℚ),(3117/119:ℚ),(-8163/34:ℚ),(43247/238:ℚ),(1510/17:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-6/119:ℚ),(15/17:ℚ),(-691/119:ℚ),(2215/119:ℚ),(-3027/119:ℚ),(-2603/119:ℚ),(16599/119:ℚ),(-23875/119:ℚ),(5813/119:ℚ),(2098/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/34:ℚ),(-233/476:ℚ),(352/119:ℚ),(-2259/238:ℚ),(2586/119:ℚ),(-685/17:ℚ),(6334/119:ℚ),(-4377/238:ℚ),(-10327/238:ℚ),(59/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(3/119:ℚ),(-29/119:ℚ),(-5/119:ℚ),(499/119:ℚ),(-1023/119:ℚ),(241/119:ℚ),(439/17:ℚ),(-49/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n3]
  all_goals ring
def num004 : List ℚ := [(1/119:ℚ),(-20/119:ℚ),(317/238:ℚ),(-193/34:ℚ),(1772/119:ℚ),(-3310/119:ℚ),(5611/119:ℚ),(-9001/119:ℚ),(10951/119:ℚ),(-914/119:ℚ),(-51579/238:ℚ),(10743/34:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-3/119:ℚ),(94/119:ℚ),(-856/119:ℚ),(3538/119:ℚ),(-1006/17:ℚ),(2370/119:ℚ),(21656/119:ℚ),(-414/1:ℚ),(5971/17:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n5]
  all_goals ring
def num006 : List ℚ := [(-1/34:ℚ),(1/2:ℚ),(-354/119:ℚ),(937/119:ℚ),(-1067/119:ℚ),(290/119:ℚ),(-1478/119:ℚ),(1045/17:ℚ),(-17683/238:ℚ),(27/2:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n6]
  all_goals ring
def num007 : List ℚ := [(5/238:ℚ),(-87/238:ℚ),(271/119:ℚ),(-768/119:ℚ),(741/119:ℚ),(2005/119:ℚ),(-78/1:ℚ),(20260/119:ℚ),(-57895/238:ℚ),(5939/34:ℚ),(-1303/17:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(9/119:ℚ),(-145/119:ℚ),(741/119:ℚ),(-1405/119:ℚ),(27/119:ℚ),(5037/119:ℚ),(-1391/17:ℚ),(343/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n8]
  all_goals ring
def num009 : List ℚ := [(-3/68:ℚ),(12/17:ℚ),(-125/34:ℚ),(771/119:ℚ),(795/119:ℚ),(-862/17:ℚ),(23503/238:ℚ),(-11125/119:ℚ),(167/4:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n9]
  all_goals ring
def num010 : List ℚ := [(3/238:ℚ),(-47/238:ℚ),(108/119:ℚ),(-52/119:ℚ),(-893/119:ℚ),(2617/119:ℚ),(-2064/119:ℚ),(-3896/119:ℚ),(3081/34:ℚ),(-4221/34:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(6/119:ℚ),(-20/17:ℚ),(810/119:ℚ),(-216/17:ℚ),(-230/119:ℚ),(5492/119:ℚ),(-1510/17:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even070.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even070.den,Blueprint.Thomson.Finite.RFCatalogue.rf1662]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even070.PairData
