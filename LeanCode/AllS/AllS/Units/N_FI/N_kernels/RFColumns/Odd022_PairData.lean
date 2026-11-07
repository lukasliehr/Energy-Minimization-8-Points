import AllS.Units.N_FI.N_kernels.RFColumns.Odd022_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd022.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-1/1:ℚ),(7/1:ℚ),(-9/1:ℚ),(-5/1:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/2:ℚ),(3/2:ℚ),(-1/2:ℚ),(-1/2:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-1/1:ℚ),(2/1:ℚ),(1/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-2/1:ℚ),(8/1:ℚ),(-18/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(2/1:ℚ),(-2/1:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n4]
  all_goals ring
def num005 : List ℚ := [(1/2:ℚ),(-1/1:ℚ),(7/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(2/1:ℚ),(-2/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(1/1:ℚ),(-1/1:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(4/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.n8]
  all_goals ring
def denominator : List ℚ := [(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd022.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd022.den,Blueprint.Thomson.Finite.RFCatalogue.rf1229]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd022.PairData
