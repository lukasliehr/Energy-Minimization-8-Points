import AllS.Units.N_FI.N_kernels.RFColumns.Odd026_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd026.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/140:ℚ),(-23/140:ℚ),(-1/20:ℚ),(487/140:ℚ),(-1583/140:ℚ),(273/20:ℚ),(-761/140:ℚ),(-199/140:ℚ),(47/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-3/70:ℚ),(-4/35:ℚ),(97/70:ℚ),(-291/70:ℚ),(459/70:ℚ),(-216/35:ℚ),(27/14:ℚ),(17/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-1/20:ℚ),(-1/20:ℚ),(117/140:ℚ),(-121/140:ℚ),(-53/28:ℚ),(57/20:ℚ),(-7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n2]
  all_goals ring
def num003 : List ℚ := [(-1/140:ℚ),(3/35:ℚ),(-31/70:ℚ),(8/7:ℚ),(11/35:ℚ),(-75/7:ℚ),(1879/70:ℚ),(-1004/35:ℚ),(577/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(4/35:ℚ),(23/35:ℚ),(-148/35:ℚ),(69/7:ℚ),(-64/5:ℚ),(45/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n4]
  all_goals ring
def num005 : List ℚ := [(1/70:ℚ),(-1/7:ℚ),(5/14:ℚ),(8/35:ℚ),(-81/70:ℚ),(13/35:ℚ),(-3/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(1/140:ℚ),(33/140:ℚ),(1/20:ℚ),(-89/20:ℚ),(307/28:ℚ),(-263/20:ℚ),(229/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(2/35:ℚ),(23/70:ℚ),(-74/35:ℚ),(69/14:ℚ),(-32/5:ℚ),(45/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(1/5:ℚ),(-4/35:ℚ),(-4/5:ℚ),(-3/35:ℚ),(-1/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd026.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd026.den,Blueprint.Thomson.Finite.RFCatalogue.rf1525]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd026.PairData
