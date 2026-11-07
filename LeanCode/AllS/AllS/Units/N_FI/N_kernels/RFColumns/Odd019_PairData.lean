import AllS.Units.N_FI.N_kernels.RFColumns.Odd019_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd019.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-17/140:ℚ),(23/28:ℚ),(-351/140:ℚ),(247/140:ℚ),(881/140:ℚ),(-223/28:ℚ),(-109/28:ℚ),(4/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(1/2:ℚ),(-67/70:ℚ),(-3/35:ℚ),(159/70:ℚ),(-23/14:ℚ),(-3/10:ℚ),(43/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-13/140:ℚ),(51/140:ℚ),(-19/140:ℚ),(-233/140:ℚ),(221/140:ℚ),(213/140:ℚ),(1/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(29/70:ℚ),(3/70:ℚ),(-143/35:ℚ),(563/70:ℚ),(143/70:ℚ),(-227/14:ℚ),(99/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(12/35:ℚ),(-47/35:ℚ),(52/35:ℚ),(69/35:ℚ),(-128/35:ℚ),(43/35:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(2/35:ℚ),(-2/5:ℚ),(6/35:ℚ),(2/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(1/28:ℚ),(37/140:ℚ),(-269/140:ℚ),(361/140:ℚ),(491/140:ℚ),(-877/140:ℚ),(-3/140:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(6/35:ℚ),(-9/14:ℚ),(18/35:ℚ),(89/70:ℚ),(-32/35:ℚ),(-27/70:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n7]
  all_goals ring
def num008 : List ℚ := [(-1/70:ℚ),(1/7:ℚ),(-3/10:ℚ),(-24/35:ℚ),(121/70:ℚ),(51/35:ℚ),(-1/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.n8]
  all_goals ring
def denominator : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-2/7:ℚ),(-32/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd019.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd019.den,Blueprint.Thomson.Finite.RFCatalogue.rf1226]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd019.PairData
