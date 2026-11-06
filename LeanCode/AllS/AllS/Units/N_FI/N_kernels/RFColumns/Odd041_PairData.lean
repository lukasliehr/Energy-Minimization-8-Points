import AllS.Units.N_FI.N_kernels.RFColumns.Odd041_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd041.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/70:ℚ),(29/70:ℚ),(-135/28:ℚ),(4021/140:ℚ),(-13689/140:ℚ),(27163/140:ℚ),(-28829/140:ℚ),(9411/140:ℚ),(1517/20:ℚ),(-1483/20:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-9/70:ℚ),(37/35:ℚ),(-11/2:ℚ),(688/35:ℚ),(-663/14:ℚ),(5053/70:ℚ),(-859/14:ℚ),(2431/140:ℚ),(482/35:ℚ),(-97/10:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-4/35:ℚ),(111/140:ℚ),(-13/4:ℚ),(1147/140:ℚ),(-1209/140:ℚ),(-2039/140:ℚ),(8247/140:ℚ),(-363/5:ℚ),(147/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-23/140:ℚ),(213/140:ℚ),(-258/35:ℚ),(663/35:ℚ),(-821/70:ℚ),(-634/7:ℚ),(11988/35:ℚ),(-82357/140:ℚ),(14981/28:ℚ),(-4547/20:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(16/35:ℚ),(-117/35:ℚ),(552/35:ℚ),(-1759/35:ℚ),(3604/35:ℚ),(-4491/35:ℚ),(3204/35:ℚ),(-144/5:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(3/70:ℚ),(-3/5:ℚ),(213/70:ℚ),(-213/35:ℚ),(-39/70:ℚ),(747/35:ℚ),(-327/10:ℚ),(21/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(3/35:ℚ),(-9/28:ℚ),(-1/4:ℚ),(1147/140:ℚ),(-5981/140:ℚ),(471/4:ℚ),(-5113/28:ℚ),(10951/70:ℚ),(-1241/20:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(8/35:ℚ),(-117/70:ℚ),(276/35:ℚ),(-1759/70:ℚ),(1802/35:ℚ),(-4491/70:ℚ),(1602/35:ℚ),(-72/5:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n7]
  all_goals ring
def num008 : List ℚ := [(-1/70:ℚ),(8/35:ℚ),(-51/35:ℚ),(163/35:ℚ),(-33/5:ℚ),(-148/35:ℚ),(1107/35:ℚ),(-1583/35:ℚ),(53/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.n8]
  all_goals ring
def denominator : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-2/7:ℚ),(-32/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd041.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd041.den,Blueprint.Thomson.Finite.RFCatalogue.rf1925]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd041.PairData
