import AllS.Units.N_FI.N_kernels.RFColumns.Odd036_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd036.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/28:ℚ),(-1/1:ℚ),(89/28:ℚ),(-29/14:ℚ),(-263/28:ℚ),(118/7:ℚ),(-61/28:ℚ),(-61/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n0]
  all_goals ring
def num001 : List ℚ := [(1/28:ℚ),(-2/7:ℚ),(19/28:ℚ),(1/14:ℚ),(-61/28:ℚ),(11/7:ℚ),(33/28:ℚ),(1/14:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n1]
  all_goals ring
def num002 : List ℚ := [(1/28:ℚ),(-5/14:ℚ),(27/28:ℚ),(3/7:ℚ),(-117/28:ℚ),(5/2:ℚ),(7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n2]
  all_goals ring
def num003 : List ℚ := [(-1/28:ℚ),(1/4:ℚ),(-23/28:ℚ),(67/28:ℚ),(-17/4:ℚ),(-71/28:ℚ),(631/28:ℚ),(-523/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n3]
  all_goals ring
def num004 : List ℚ := [(-1/28:ℚ),(1/14:ℚ),(19/28:ℚ),(-13/7:ℚ),(-19/28:ℚ),(57/14:ℚ),(1/28:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n4]
  all_goals ring
def num005 : List ℚ := [(1/14:ℚ),(-4/7:ℚ),(10/7:ℚ),(0/1:ℚ),(-81/14:ℚ),(6/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n5]
  all_goals ring
def num006 : List ℚ := [(-1/28:ℚ),(1/7:ℚ),(19/28:ℚ),(-27/7:ℚ),(11/4:ℚ),(60/7:ℚ),(-391/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n6]
  all_goals ring
def num007 : List ℚ := [(-1/14:ℚ),(4/7:ℚ),(-8/7:ℚ),(-8/7:ℚ),(53/14:ℚ),(-6/7:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/14:ℚ),(-2/7:ℚ),(2/7:ℚ),(0/1:ℚ),(-7/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd036.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd036.den,Blueprint.Thomson.Finite.RFCatalogue.rf1535]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd036.PairData
