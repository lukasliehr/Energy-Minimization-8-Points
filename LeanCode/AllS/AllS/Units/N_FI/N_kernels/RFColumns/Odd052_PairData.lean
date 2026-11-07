import AllS.Units.N_FI.N_kernels.RFColumns.Odd052_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd052.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-11/70:ℚ),(197/140:ℚ),(-45/7:ℚ),(1047/70:ℚ),(-62/5:ℚ),(-969/70:ℚ),(993/35:ℚ),(353/140:ℚ),(-165/14:ℚ),(-2563/140:ℚ),(-44/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-9/70:ℚ),(129/140:ℚ),(-461/140:ℚ),(81/14:ℚ),(-219/70:ℚ),(-39/10:ℚ),(30/7:ℚ),(-3/140:ℚ),(96/35:ℚ),(-263/140:ℚ),(-39/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-4/35:ℚ),(93/140:ℚ),(-52/35:ℚ),(-29/70:ℚ),(244/35:ℚ),(-79/10:ℚ),(-4/1:ℚ),(761/140:ℚ),(32/5:ℚ),(7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n2]
  all_goals ring
def num003 : List ℚ := [(1/140:ℚ),(-17/140:ℚ),(107/140:ℚ),(-251/140:ℚ),(-23/10:ℚ),(1571/70:ℚ),(-3231/70:ℚ),(1557/70:ℚ),(5297/140:ℚ),(-865/28:ℚ),(-2269/140:ℚ),(-627/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(16/35:ℚ),(-99/35:ℚ),(292/35:ℚ),(-381/35:ℚ),(32/35:ℚ),(383/35:ℚ),(-212/35:ℚ),(26/7:ℚ),(-32/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n4]
  all_goals ring
def num005 : List ℚ := [(-1/140:ℚ),(13/140:ℚ),(-13/35:ℚ),(6/35:ℚ),(27/14:ℚ),(-221/70:ℚ),(-51/35:ℚ),(194/35:ℚ),(23/28:ℚ),(15/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(3/35:ℚ),(-29/140:ℚ),(-47/35:ℚ),(613/70:ℚ),(-125/7:ℚ),(617/70:ℚ),(523/35:ℚ),(-1609/140:ℚ),(-94/35:ℚ),(-177/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(8/35:ℚ),(-7/5:ℚ),(281/70:ℚ),(-169/35:ℚ),(-9/14:ℚ),(199/35:ℚ),(111/70:ℚ),(-409/70:ℚ),(17/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n7]
  all_goals ring
def num008 : List ℚ := [(-1/140:ℚ),(13/140:ℚ),(-13/35:ℚ),(6/35:ℚ),(27/14:ℚ),(-221/70:ℚ),(-51/35:ℚ),(194/35:ℚ),(23/28:ℚ),(15/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd052.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd052.den,Blueprint.Thomson.Finite.RFCatalogue.rf1936]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd052.PairData
