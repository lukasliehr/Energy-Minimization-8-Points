import AllS.Units.N_FI.N_kernels.RFColumns.Odd054_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd054.PairData
def num000 : List ℚ := [(0/1:ℚ),(-5/28:ℚ),(55/28:ℚ),(-227/28:ℚ),(347/28:ℚ),(263/28:ℚ),(-1487/28:ℚ),(1499/28:ℚ),(-21/4:ℚ),(-213/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n0]
  all_goals ring
def num001 : List ℚ := [(-1/14:ℚ),(5/7:ℚ),(-17/7:ℚ),(2/1:ℚ),(39/7:ℚ),(-11/1:ℚ),(3/1:ℚ),(18/7:ℚ),(-5/14:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n1]
  all_goals ring
def num002 : List ℚ := [(-1/14:ℚ),(11/14:ℚ),(-37/14:ℚ),(15/14:ℚ),(129/14:ℚ),(-187/14:ℚ),(3/2:ℚ),(7/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n2]
  all_goals ring
def num003 : List ℚ := [(1/28:ℚ),(-9/28:ℚ),(25/14:ℚ),(-227/28:ℚ),(145/7:ℚ),(-267/28:ℚ),(-907/14:ℚ),(3159/28:ℚ),(-1473/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(2/7:ℚ),(-16/7:ℚ),(38/7:ℚ),(4/7:ℚ),(-110/7:ℚ),(92/7:ℚ),(-10/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n4]
  all_goals ring
def num005 : List ℚ := [(-1/7:ℚ),(9/7:ℚ),(-4/1:ℚ),(20/7:ℚ),(81/7:ℚ),(-165/7:ℚ),(12/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n5]
  all_goals ring
def num006 : List ℚ := [(1/14:ℚ),(-2/7:ℚ),(-10/7:ℚ),(123/14:ℚ),(-117/14:ℚ),(-142/7:ℚ),(232/7:ℚ),(29/14:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n6]
  all_goals ring
def num007 : List ℚ := [(1/7:ℚ),(-8/7:ℚ),(19/7:ℚ),(2/7:ℚ),(-55/7:ℚ),(46/7:ℚ),(-5/7:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n7]
  all_goals ring
def num008 : List ℚ := [(1/28:ℚ),(-2/7:ℚ),(1/4:ℚ),(17/7:ℚ),(-19/4:ℚ),(-23/7:ℚ),(59/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd054.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd054.den,Blueprint.Thomson.Finite.RFCatalogue.rf1938]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd054.PairData
