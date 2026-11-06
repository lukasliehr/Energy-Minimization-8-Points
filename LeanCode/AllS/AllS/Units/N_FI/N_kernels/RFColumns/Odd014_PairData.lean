import AllS.Units.N_FI.N_kernels.RFColumns.Odd014_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd014.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/20:ℚ),(29/70:ℚ),(-13/28:ℚ),(-134/35:ℚ),(1731/140:ℚ),(-617/70:ℚ),(-93/20:ℚ),(16/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n0]
  all_goals ring
def num001 : List ℚ := [(-3/140:ℚ),(3/20:ℚ),(-1/140:ℚ),(-237/140:ℚ),(591/140:ℚ),(-641/140:ℚ),(261/140:ℚ),(137/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n1]
  all_goals ring
def num002 : List ℚ := [(-3/140:ℚ),(13/70:ℚ),(-9/28:ℚ),(-4/7:ℚ),(151/140:ℚ),(-13/70:ℚ),(3/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-1/20:ℚ),(31/140:ℚ),(-25/28:ℚ),(-33/28:ℚ),(367/28:ℚ),(-2827/140:ℚ),(361/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(3/35:ℚ),(-3/7:ℚ),(-4/5:ℚ),(184/35:ℚ),(-41/5:ℚ),(207/35:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n4]
  all_goals ring
def num005 : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-9/35:ℚ),(-39/35:ℚ),(38/35:ℚ),(1/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n5]
  all_goals ring
def num006 : List ℚ := [(3/140:ℚ),(-3/70:ℚ),(-15/28:ℚ),(4/35:ℚ),(881/140:ℚ),(-91/10:ℚ),(583/140:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n6]
  all_goals ring
def num007 : List ℚ := [(3/70:ℚ),(-3/14:ℚ),(-2/5:ℚ),(92/35:ℚ),(-41/10:ℚ),(207/70:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n7]
  all_goals ring
def num008 : List ℚ := [(1/70:ℚ),(-1/14:ℚ),(-4/35:ℚ),(2/7:ℚ),(79/70:ℚ),(3/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd014.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd014.den,Blueprint.Thomson.Finite.RFCatalogue.rf1221]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd014.PairData
