import AllS.Units.N_FI.N_kernels.RFColumns.Odd051_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd051.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/2:ℚ),(-33/7:ℚ),(108/7:ℚ),(-72/7:ℚ),(-390/7:ℚ),(965/7:ℚ),(-740/7:ℚ),(12/7:ℚ),(421/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n0]
  all_goals ring
def num001 : List ℚ := [(3/14:ℚ),(-12/7:ℚ),(117/28:ℚ),(13/14:ℚ),(-611/28:ℚ),(285/7:ℚ),(-865/28:ℚ),(41/14:ℚ),(281/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n1]
  all_goals ring
def num002 : List ℚ := [(3/14:ℚ),(-25/14:ℚ),(57/14:ℚ),(25/14:ℚ),(-227/14:ℚ),(209/14:ℚ),(1/2:ℚ),(-7/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n2]
  all_goals ring
def num003 : List ℚ := [(-1/14:ℚ),(9/14:ℚ),(-57/14:ℚ),(237/14:ℚ),(-415/14:ℚ),(-345/14:ℚ),(2473/14:ℚ),(-3373/14:ℚ),(800/7:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-6/7:ℚ),(36/7:ℚ),(-51/7:ℚ),(-92/7:ℚ),(376/7:ℚ),(-480/7:ℚ),(281/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n4]
  all_goals ring
def num005 : List ℚ := [(2/7:ℚ),(-18/7:ℚ),(48/7:ℚ),(-4/7:ℚ),(-158/7:ℚ),(214/7:ℚ),(-12/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n5]
  all_goals ring
def num006 : List ℚ := [(-3/14:ℚ),(1/2:ℚ),(61/14:ℚ),(-31/2:ℚ),(-13/14:ℚ),(897/14:ℚ),(-1373/14:ℚ),(513/14:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n6]
  all_goals ring
def num007 : List ℚ := [(-13/28:ℚ),(39/14:ℚ),(-109/28:ℚ),(-7/1:ℚ),(785/28:ℚ),(-493/14:ℚ),(569/28:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n7]
  all_goals ring
def num008 : List ℚ := [(-1/7:ℚ),(5/7:ℚ),(2/7:ℚ),(-4/1:ℚ),(13/7:ℚ),(15/7:ℚ),(-10/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd051.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd051.den,Blueprint.Thomson.Finite.RFCatalogue.rf1935]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd051.PairData
