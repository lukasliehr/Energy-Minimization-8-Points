import AllS.Units.N_FI.N_kernels.RFColumns.Odd030_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd030.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/28:ℚ),(11/28:ℚ),(-27/20:ℚ),(27/28:ℚ),(373/140:ℚ),(-87/140:ℚ),(-1459/140:ℚ),(937/140:ℚ),(156/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n0]
  all_goals ring
def num001 : List ℚ := [(-1/70:ℚ),(19/140:ℚ),(-47/140:ℚ),(-9/140:ℚ),(53/140:ℚ),(373/140:ℚ),(-809/140:ℚ),(39/20:ℚ),(277/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n1]
  all_goals ring
def num002 : List ℚ := [(-1/70:ℚ),(1/7:ℚ),(-12/35:ℚ),(-29/70:ℚ),(25/14:ℚ),(-1/35:ℚ),(-54/35:ℚ),(-1/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-11/140:ℚ),(29/70:ℚ),(-209/140:ℚ),(157/70:ℚ),(75/28:ℚ),(-481/70:ℚ),(-1387/140:ℚ),(2461/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(2/35:ℚ),(-31/70:ℚ),(47/70:ℚ),(23/35:ℚ),(19/35:ℚ),(-99/14:ℚ),(519/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n4]
  all_goals ring
def num005 : List ℚ := [(-3/140:ℚ),(17/70:ℚ),(-109/140:ℚ),(-2/35:ℚ),(463/140:ℚ),(-33/14:ℚ),(-5/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n5]
  all_goals ring
def num006 : List ℚ := [(1/70:ℚ),(-2/35:ℚ),(-5/14:ℚ),(54/35:ℚ),(-1/10:ℚ),(-53/35:ℚ),(-457/70:ℚ),(277/35:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n6]
  all_goals ring
def num007 : List ℚ := [(1/35:ℚ),(-3/14:ℚ),(19/70:ℚ),(16/35:ℚ),(3/7:ℚ),(-281/70:ℚ),(277/70:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n7]
  all_goals ring
def num008 : List ℚ := [(1/140:ℚ),(-3/70:ℚ),(-9/140:ℚ),(18/35:ℚ),(27/140:ℚ),(-89/70:ℚ),(-1/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd030.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd030.den,Blueprint.Thomson.Finite.RFCatalogue.rf1529]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd030.PairData
