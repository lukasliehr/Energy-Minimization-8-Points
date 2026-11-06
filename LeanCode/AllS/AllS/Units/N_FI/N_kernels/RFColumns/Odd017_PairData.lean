import AllS.Units.N_FI.N_kernels.RFColumns.Odd017_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd017.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/140:ℚ),(-1/5:ℚ),(57/140:ℚ),(27/35:ℚ),(-319/140:ℚ),(-88/35:ℚ),(803/140:ℚ),(92/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-1/20:ℚ),(1/140:ℚ),(7/20:ℚ),(3/28:ℚ),(-233/140:ℚ),(19/28:ℚ),(79/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-2/35:ℚ),(1/20:ℚ),(13/35:ℚ),(-37/140:ℚ),(-27/35:ℚ),(-1/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n2]
  all_goals ring
def num003 : List ℚ := [(-1/140:ℚ),(11/140:ℚ),(-7/20:ℚ),(109/140:ℚ),(41/140:ℚ),(-131/28:ℚ),(47/20:ℚ),(1367/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/70:ℚ),(1/70:ℚ),(17/35:ℚ),(-17/35:ℚ),(-193/70:ℚ),(193/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n4]
  all_goals ring
def num005 : List ℚ := [(1/70:ℚ),(-1/7:ℚ),(11/35:ℚ),(4/7:ℚ),(-111/70:ℚ),(-1/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(1/70:ℚ),(31/140:ℚ),(-12/35:ℚ),(-5/4:ℚ),(1/10:ℚ),(561/140:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(1/14:ℚ),(4/35:ℚ),(-2/5:ℚ),(-9/10:ℚ),(79/70:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/70:ℚ),(3/35:ℚ),(2/35:ℚ),(-19/35:ℚ),(-1/2:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd017.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd017.den,Blueprint.Thomson.Finite.RFCatalogue.rf1224]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd017.PairData
