import AllS.Units.N_FI.N_kernels.RFColumns.Odd021_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd021.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/140:ℚ),(1/7:ℚ),(-37/35:ℚ),(117/35:ℚ),(-209/70:ℚ),(-169/35:ℚ),(209/35:ℚ),(27/35:ℚ),(183/28:ℚ),(108/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n0]
  all_goals ring
def num001 : List ℚ := [(-1/140:ℚ),(3/28:ℚ),(-41/70:ℚ),(47/35:ℚ),(-6/7:ℚ),(-15/14:ℚ),(141/70:ℚ),(-81/35:ℚ),(81/140:ℚ),(111/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n1]
  all_goals ring
def num002 : List ℚ := [(-1/140:ℚ),(3/35:ℚ),(-2/7:ℚ),(-3/35:ℚ),(101/70:ℚ),(-1/5:ℚ),(-54/35:ℚ),(-81/35:ℚ),(-3/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n2]
  all_goals ring
def num003 : List ℚ := [(-1/140:ℚ),(13/140:ℚ),(-12/35:ℚ),(-3/10:ℚ),(327/70:ℚ),(-323/35:ℚ),(6/35:ℚ),(857/70:ℚ),(-17/28:ℚ),(1623/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(3/70:ℚ),(-37/70:ℚ),(149/70:ℚ),(-179/70:ℚ),(-123/70:ℚ),(57/14:ℚ),(-57/14:ℚ),(187/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n4]
  all_goals ring
def num005 : List ℚ := [(1/70:ℚ),(-1/7:ℚ),(3/10:ℚ),(24/35:ℚ),(-25/14:ℚ),(-37/35:ℚ),(23/70:ℚ),(-2/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n5]
  all_goals ring
def num006 : List ℚ := [(1/140:ℚ),(-1/14:ℚ),(1/14:ℚ),(17/14:ℚ),(-27/7:ℚ),(149/70:ℚ),(99/70:ℚ),(-117/70:ℚ),(619/140:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n6]
  all_goals ring
def num007 : List ℚ := [(1/70:ℚ),(-13/70:ℚ),(53/70:ℚ),(-51/70:ℚ),(-69/70:ℚ),(-19/70:ℚ),(127/70:ℚ),(-29/70:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-1/5:ℚ),(53/70:ℚ),(2/35:ℚ),(-221/70:ℚ),(13/35:ℚ),(-3/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd021.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd021.den,Blueprint.Thomson.Finite.RFCatalogue.rf1228]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd021.PairData
