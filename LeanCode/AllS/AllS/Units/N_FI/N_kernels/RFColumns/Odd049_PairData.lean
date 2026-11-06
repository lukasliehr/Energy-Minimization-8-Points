import AllS.Units.N_FI.N_kernels.RFColumns.Odd049_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd049.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-3/35:ℚ),(17/70:ℚ),(69/70:ℚ),(-271/35:ℚ),(1251/70:ℚ),(-169/14:ℚ),(-941/70:ℚ),(1931/140:ℚ),(699/70:ℚ),(10/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-3/14:ℚ),(89/70:ℚ),(-26/7:ℚ),(351/70:ℚ),(-34/35:ℚ),(-253/70:ℚ),(4/5:ℚ),(6/5:ℚ),(3/14:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-1/10:ℚ),(1/2:ℚ),(-61/70:ℚ),(-34/35:ℚ),(351/70:ℚ),(-187/70:ℚ),(-267/70:ℚ),(-3/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n2]
  all_goals ring
def num003 : List ℚ := [(-1/140:ℚ),(4/35:ℚ),(-5/7:ℚ),(29/14:ℚ),(-51/35:ℚ),(-653/70:ℚ),(2291/70:ℚ),(-2873/70:ℚ),(121/28:ℚ),(1917/70:ℚ),(59/14:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-2/35:ℚ),(26/35:ℚ),(-128/35:ℚ),(58/7:ℚ),(-50/7:ℚ),(-74/35:ℚ),(108/35:ℚ),(6/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n4]
  all_goals ring
def num005 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(33/70:ℚ),(-9/14:ℚ),(-9/7:ℚ),(303/70:ℚ),(-137/70:ℚ),(-331/70:ℚ),(1/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n5]
  all_goals ring
def num006 : List ℚ := [(0/1:ℚ),(-1/140:ℚ),(3/70:ℚ),(17/70:ℚ),(-39/14:ℚ),(324/35:ℚ),(-851/70:ℚ),(39/70:ℚ),(69/10:ℚ),(45/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(5/14:ℚ),(-59/35:ℚ),(261/70:ℚ),(-17/5:ℚ),(-1/14:ℚ),(-29/35:ℚ),(27/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n7]
  all_goals ring
def num008 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(33/70:ℚ),(-9/14:ℚ),(-9/7:ℚ),(303/70:ℚ),(-137/70:ℚ),(-331/70:ℚ),(1/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.n8]
  all_goals ring
def denominator : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-2/7:ℚ),(-32/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd049.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd049.den,Blueprint.Thomson.Finite.RFCatalogue.rf1933]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd049.PairData
