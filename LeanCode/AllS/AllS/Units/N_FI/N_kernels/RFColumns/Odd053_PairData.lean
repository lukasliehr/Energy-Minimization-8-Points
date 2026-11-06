import AllS.Units.N_FI.N_kernels.RFColumns.Odd053_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd053.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/280:ℚ),(-3/20:ℚ),(3/4:ℚ),(-193/140:ℚ),(-61/70:ℚ),(981/140:ℚ),(-159/20:ℚ),(-97/20:ℚ),(3089/280:ℚ),(162/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n0]
  all_goals ring
def num001 : List ℚ := [(1/280:ℚ),(-13/280:ℚ),(29/140:ℚ),(-37/140:ℚ),(-24/35:ℚ),(76/35:ℚ),(-29/140:ℚ),(-77/20:ℚ),(83/56:ℚ),(333/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n1]
  all_goals ring
def num002 : List ℚ := [(1/280:ℚ),(-1/20:ℚ),(1/4:ℚ),(-59/140:ℚ),(-43/70:ℚ),(383/140:ℚ),(-23/28:ℚ),(-59/20:ℚ),(-7/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n2]
  all_goals ring
def num003 : List ℚ := [(-1/280:ℚ),(13/280:ℚ),(-31/140:ℚ),(19/35:ℚ),(-37/35:ℚ),(167/140:ℚ),(17/4:ℚ),(-514/35:ℚ),(397/56:ℚ),(5149/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/140:ℚ),(11/140:ℚ),(-39/140:ℚ),(17/140:ℚ),(45/28:ℚ),(-339/140:ℚ),(-101/28:ℚ),(631/140:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n4]
  all_goals ring
def num005 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(13/28:ℚ),(-22/35:ℚ),(-141/140:ℚ),(253/70:ℚ),(-421/140:ℚ),(-3/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n5]
  all_goals ring
def num006 : List ℚ := [(-1/280:ℚ),(1/35:ℚ),(1/70:ℚ),(-7/10:ℚ),(57/28:ℚ),(13/35:ℚ),(-621/70:ℚ),(65/14:ℚ),(2487/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n6]
  all_goals ring
def num007 : List ℚ := [(-1/140:ℚ),(11/140:ℚ),(-41/140:ℚ),(47/140:ℚ),(3/4:ℚ),(-331/140:ℚ),(17/140:ℚ),(193/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/140:ℚ),(-4/35:ℚ),(71/140:ℚ),(-1/5:ℚ),(-293/140:ℚ),(43/35:ℚ),(-1/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd053.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd053.den,Blueprint.Thomson.Finite.RFCatalogue.rf1937]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd053.PairData
