import AllS.Units.N_FI.N_kernels.RFColumns.Odd028_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd028.PairData
def num000 : List ℚ := [(0/1:ℚ),(-3/2:ℚ),(83/14:ℚ),(155/14:ℚ),(-1489/14:ℚ),(3153/14:ℚ),(-2591/14:ℚ),(361/14:ℚ),(123/2:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n0]
  all_goals ring
def num001 : List ℚ := [(-17/28:ℚ),(31/28:ℚ),(317/28:ℚ),(-1471/28:ℚ),(2657/28:ℚ),(-2039/28:ℚ),(-45/28:ℚ),(81/4:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n1]
  all_goals ring
def num002 : List ℚ := [(-3/4:ℚ),(7/2:ℚ),(-1/4:ℚ),(-11/1:ℚ),(43/4:ℚ),(-1/2:ℚ),(-7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n2]
  all_goals ring
def num003 : List ℚ := [(2/7:ℚ),(-10/7:ℚ),(55/7:ℚ),(-75/7:ℚ),(-508/7:ℚ),(2060/7:ℚ),(-2813/7:ℚ),(239/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(17/7:ℚ),(3/7:ℚ),(-42/1:ℚ),(886/7:ℚ),(-1179/7:ℚ),(81/1:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n4]
  all_goals ring
def num005 : List ℚ := [(-1/1:ℚ),(5/1:ℚ),(-2/1:ℚ),(-14/1:ℚ),(19/1:ℚ),(-7/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n5]
  all_goals ring
def num006 : List ℚ := [(5/7:ℚ),(4/7:ℚ),(-37/7:ℚ),(-228/7:ℚ),(129/1:ℚ),(-1312/7:ℚ),(95/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n6]
  all_goals ring
def num007 : List ℚ := [(17/14:ℚ),(3/14:ℚ),(-21/1:ℚ),(443/7:ℚ),(-1179/14:ℚ),(81/2:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n7]
  all_goals ring
def num008 : List ℚ := [(3/7:ℚ),(-3/7:ℚ),(-30/7:ℚ),(-2/7:ℚ),(-5/7:ℚ),(-13/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd028.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd028.den,Blueprint.Thomson.Finite.RFCatalogue.rf1527]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd028.PairData
