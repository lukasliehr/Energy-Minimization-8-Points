import AllS.Units.N_FI.N_kernels.RFColumns.Odd029_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd029.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-1/10:ℚ),(47/70:ℚ),(-43/14:ℚ),(10/1:ℚ),(-1443/70:ℚ),(1409/70:ℚ),(311/70:ℚ),(-2361/140:ℚ),(-39/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-3/28:ℚ),(47/70:ℚ),(-82/35:ℚ),(179/35:ℚ),(-487/70:ℚ),(57/14:ℚ),(68/35:ℚ),(-261/140:ℚ),(-15/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(1/2:ℚ),(-69/70:ℚ),(2/35:ℚ),(223/70:ℚ),(-95/14:ℚ),(317/70:ℚ),(13/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-17/140:ℚ),(27/35:ℚ),(-149/70:ℚ),(57/70:ℚ),(423/35:ℚ),(-201/5:ℚ),(4229/70:ℚ),(-935/28:ℚ),(-463/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(5/14:ℚ),(-64/35:ℚ),(377/70:ℚ),(-373/35:ℚ),(907/70:ℚ),(-194/35:ℚ),(-9/14:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-6/35:ℚ),(47/70:ℚ),(-4/7:ℚ),(-169/70:ℚ),(162/35:ℚ),(3/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(2/35:ℚ),(0/1:ℚ),(-6/5:ℚ),(353/70:ℚ),(-86/7:ℚ),(96/5:ℚ),(-74/7:ℚ),(-109/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(13/70:ℚ),(-69/70:ℚ),(29/10:ℚ),(-379/70:ℚ),(419/70:ℚ),(-111/70:ℚ),(-15/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n7]
  all_goals ring
def num008 : List ℚ := [(-1/70:ℚ),(6/35:ℚ),(-47/70:ℚ),(26/35:ℚ),(89/70:ℚ),(-158/35:ℚ),(327/70:ℚ),(2/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.n8]
  all_goals ring
def denominator : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-2/7:ℚ),(-32/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd029.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd029.den,Blueprint.Thomson.Finite.RFCatalogue.rf1528]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd029.PairData
