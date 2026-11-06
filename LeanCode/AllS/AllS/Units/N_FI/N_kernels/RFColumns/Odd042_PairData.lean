import AllS.Units.N_FI.N_kernels.RFColumns.Odd042_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd042.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/28:ℚ),(53/140:ℚ),(-163/140:ℚ),(-71/140:ℚ),(217/20:ℚ),(-3893/140:ℚ),(5203/140:ℚ),(-3793/140:ℚ),(-3/10:ℚ),(66/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n0]
  all_goals ring
def num001 : List ℚ := [(-1/70:ℚ),(9/70:ℚ),(-3/14:ℚ),(-79/70:ℚ),(197/35:ℚ),(-404/35:ℚ),(199/14:ℚ),(-125/14:ℚ),(-101/70:ℚ),(59/14:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n1]
  all_goals ring
def num002 : List ℚ := [(-1/70:ℚ),(19/140:ℚ),(-37/140:ℚ),(-97/140:ℚ),(59/28:ℚ),(3/20:ℚ),(-411/140:ℚ),(47/20:ℚ),(-7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-11/140:ℚ),(61/140:ℚ),(-241/140:ℚ),(403/140:ℚ),(813/140:ℚ),(-135/4:ℚ),(8849/140:ℚ),(-2459/35:ℚ),(507/14:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(2/35:ℚ),(-2/5:ℚ),(1/7:ℚ),(143/35:ℚ),(-458/35:ℚ),(802/35:ℚ),(-901/35:ℚ),(97/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n4]
  all_goals ring
def num005 : List ℚ := [(-3/140:ℚ),(31/140:ℚ),(-83/140:ℚ),(-7/20:ℚ),(347/140:ℚ),(-111/140:ℚ),(-17/28:ℚ),(-5/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n5]
  all_goals ring
def num006 : List ℚ := [(1/70:ℚ),(-1/20:ℚ),(-11/28:ℚ),(27/20:ℚ),(73/28:ℚ),(-303/20:ℚ),(537/20:ℚ),(-3933/140:ℚ),(437/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n6]
  all_goals ring
def num007 : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(1/14:ℚ),(143/70:ℚ),(-229/35:ℚ),(401/35:ℚ),(-901/70:ℚ),(97/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n7]
  all_goals ring
def num008 : List ℚ := [(1/140:ℚ),(-1/28:ℚ),(-19/140:ℚ),(111/140:ℚ),(-57/140:ℚ),(-29/20:ℚ),(95/28:ℚ),(-5/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd042.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd042.den,Blueprint.Thomson.Finite.RFCatalogue.rf1926]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd042.PairData
