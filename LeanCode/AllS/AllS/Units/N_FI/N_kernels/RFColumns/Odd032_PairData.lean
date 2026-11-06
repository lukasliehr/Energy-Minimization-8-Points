import AllS.Units.N_FI.N_kernels.RFColumns.Odd032_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd032.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/14:ℚ),(-41/35:ℚ),(38/5:ℚ),(-842/35:ℚ),(241/7:ℚ),(-136/35:ℚ),(-1346/35:ℚ),(314/35:ℚ),(2081/70:ℚ),(61/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n0]
  all_goals ring
def num001 : List ℚ := [(-1/140:ℚ),(1/7:ℚ),(-8/7:ℚ),(164/35:ℚ),(-51/5:ℚ),(349/35:ℚ),(37/70:ℚ),(-202/35:ℚ),(-339/140:ℚ),(20/7:ℚ),(19/14:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n1]
  all_goals ring
def num002 : List ℚ := [(-1/140:ℚ),(17/140:ℚ),(-27/35:ℚ),(72/35:ℚ),(-9/14:ℚ),(-113/14:ℚ),(491/35:ℚ),(0/1:ℚ),(-1509/140:ℚ),(-13/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n2]
  all_goals ring
def num003 : List ℚ := [(-1/70:ℚ),(17/70:ℚ),(-111/70:ℚ),(156/35:ℚ),(-19/35:ℚ),(-221/7:ℚ),(2999/35:ℚ),(-564/7:ℚ),(-1017/70:ℚ),(653/14:ℚ),(397/14:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/35:ℚ),(-18/35:ℚ),(25/7:ℚ),(-424/35:ℚ),(141/7:ℚ),(-82/7:ℚ),(-27/5:ℚ),(4/7:ℚ),(38/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n4]
  all_goals ring
def num005 : List ℚ := [(1/70:ℚ),(-1/5:ℚ),(33/35:ℚ),(-9/7:ℚ),(-86/35:ℚ),(271/35:ℚ),(-97/35:ℚ),(-29/5:ℚ),(-7/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n5]
  all_goals ring
def num006 : List ℚ := [(1/140:ℚ),(-13/140:ℚ),(9/35:ℚ),(53/35:ℚ),(-803/70:ℚ),(395/14:ℚ),(-901/35:ℚ),(-27/5:ℚ),(227/20:ℚ),(243/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n6]
  all_goals ring
def num007 : List ℚ := [(1/70:ℚ),(-9/35:ℚ),(25/14:ℚ),(-214/35:ℚ),(741/70:ℚ),(-241/35:ℚ),(-277/70:ℚ),(144/35:ℚ),(5/7:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n7]
  all_goals ring
def num008 : List ℚ := [(1/70:ℚ),(-1/5:ℚ),(33/35:ℚ),(-9/7:ℚ),(-86/35:ℚ),(271/35:ℚ),(-97/35:ℚ),(-29/5:ℚ),(-7/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd032.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd032.den,Blueprint.Thomson.Finite.RFCatalogue.rf1531]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd032.PairData
