import AllS.Units.N_FI.N_kernels.RFColumns.Odd056_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd056.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/14:ℚ),(-25/28:ℚ),(59/14:ℚ),(-235/28:ℚ),(0/1:ℚ),(941/28:ℚ),(-825/14:ℚ),(559/28:ℚ),(289/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n0]
  all_goals ring
def num001 : List ℚ := [(1/28:ℚ),(-5/14:ℚ),(5/4:ℚ),(-9/7:ℚ),(-11/4:ℚ),(123/14:ℚ),(-33/4:ℚ),(8/7:ℚ),(18/7:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n1]
  all_goals ring
def num002 : List ℚ := [(1/28:ℚ),(-5/14:ℚ),(5/4:ℚ),(-8/7:ℚ),(-101/28:ℚ),(123/14:ℚ),(-87/28:ℚ),(-3/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/14:ℚ),(-25/28:ℚ),(5/1:ℚ),(-391/28:ℚ),(149/14:ℚ),(1013/28:ℚ),(-688/7:ℚ),(2067/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/14:ℚ),(5/7:ℚ),(-5/2:ℚ),(2/1:ℚ),(101/14:ℚ),(-111/7:ℚ),(151/14:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n4]
  all_goals ring
def num005 : List ℚ := [(1/28:ℚ),(-1/2:ℚ),(59/28:ℚ),(-17/7:ℚ),(-117/28:ℚ),(197/14:ℚ),(-41/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n5]
  all_goals ring
def num006 : List ℚ := [(-1/28:ℚ),(1/7:ℚ),(17/28:ℚ),(-57/14:ℚ),(141/28:ℚ),(74/7:ℚ),(-99/4:ℚ),(95/14:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n6]
  all_goals ring
def num007 : List ℚ := [(-3/28:ℚ),(11/14:ℚ),(-53/28:ℚ),(5/7:ℚ),(25/4:ℚ),(-23/2:ℚ),(193/28:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n7]
  all_goals ring
def num008 : List ℚ := [(-1/28:ℚ),(3/14:ℚ),(-3/28:ℚ),(-15/7:ℚ),(149/28:ℚ),(9/2:ℚ),(-63/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd056.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd056.den,Blueprint.Thomson.Finite.RFCatalogue.rf1940]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd056.PairData
