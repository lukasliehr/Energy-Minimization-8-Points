import AllS.Units.N_FI.N_kernels.RFColumns.Odd060_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/4:ℚ),(-23/4:ℚ),(18/1:ℚ),(-57/2:ℚ),(79/4:ℚ),(5/4:ℚ),(-11/2:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n0]
  all_goals ring
def num001 : List ℚ := []
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n1]
  all_goals ring
def num002 : List ℚ := []
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n2]
  all_goals ring
def num003 : List ℚ := [(-3/4:ℚ),(23/4:ℚ),(-81/4:ℚ),(85/2:ℚ),(-227/4:ℚ),(183/4:ℚ),(-73/4:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n3]
  all_goals ring
def num004 : List ℚ := []
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n4]
  all_goals ring
def num005 : List ℚ := []
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(1/2:ℚ),(-9/2:ℚ),(23/2:ℚ),(-29/2:ℚ),(7/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n6]
  all_goals ring
def num007 : List ℚ := []
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n7]
  all_goals ring
def num008 : List ℚ := [(7/4:ℚ),(-19/2:ℚ),(51/2:ℚ),(-65/2:ℚ),(71/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.n8]
  all_goals ring
def denominator : List ℚ := [(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd060.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.den,Blueprint.Thomson.Finite.RFCatalogue.rf1327]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData
