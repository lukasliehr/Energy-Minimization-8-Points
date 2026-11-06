import AllS.Units.N_FI.N_kernels.RFColumns.Odd048_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd048.PairData
def num000 : List ℚ := [(0/1:ℚ),(-17/14:ℚ),(69/7:ℚ),(-204/7:ℚ),(227/7:ℚ),(-31/7:ℚ),(151/7:ℚ),(-576/7:ℚ),(39/1:ℚ),(65/2:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n0]
  all_goals ring
def num001 : List ℚ := [(-1/2:ℚ),(95/28:ℚ),(-221/28:ℚ),(261/28:ℚ),(-575/28:ℚ),(1537/28:ℚ),(-1675/28:ℚ),(123/28:ℚ),(67/4:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n1]
  all_goals ring
def num002 : List ℚ := [(-1/2:ℚ),(7/2:ℚ),(-11/2:ℚ),(-15/2:ℚ),(49/2:ℚ),(-31/2:ℚ),(-5/2:ℚ),(7/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n2]
  all_goals ring
def num003 : List ℚ := [(3/14:ℚ),(-11/7:ℚ),(60/7:ℚ),(-218/7:ℚ),(348/7:ℚ),(-83/7:ℚ),(-2/7:ℚ),(-760/7:ℚ),(263/2:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(2/1:ℚ),(-67/7:ℚ),(101/7:ℚ),(-18/1:ℚ),(424/7:ℚ),(-815/7:ℚ),(67/1:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n4]
  all_goals ring
def num005 : List ℚ := [(-3/4:ℚ),(11/2:ℚ),(-41/4:ℚ),(-7/1:ℚ),(155/4:ℚ),(-77/2:ℚ),(49/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n5]
  all_goals ring
def num006 : List ℚ := [(1/2:ℚ),(-1/2:ℚ),(-145/14:ℚ),(417/14:ℚ),(-411/14:ℚ),(555/14:ℚ),(-1147/14:ℚ),(141/2:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n6]
  all_goals ring
def num007 : List ℚ := [(1/1:ℚ),(-67/14:ℚ),(101/14:ℚ),(-9/1:ℚ),(212/7:ℚ),(-815/14:ℚ),(67/2:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n7]
  all_goals ring
def num008 : List ℚ := [(2/7:ℚ),(-1/1:ℚ),(-13/7:ℚ),(38/7:ℚ),(20/7:ℚ),(-47/7:ℚ),(1/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd048.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd048.den,Blueprint.Thomson.Finite.RFCatalogue.rf1932]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd048.PairData
