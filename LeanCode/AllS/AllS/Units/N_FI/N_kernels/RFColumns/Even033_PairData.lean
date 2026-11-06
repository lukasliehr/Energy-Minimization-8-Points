import AllS.Units.N_FI.N_kernels.RFColumns.Even033_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even033.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/68:ℚ),(3/17:ℚ),(-55/68:ℚ),(77/34:ℚ),(-295/68:ℚ),(82/17:ℚ),(-113/68:ℚ),(-47/34:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/34:ℚ),(9/34:ℚ),(-12/17:ℚ),(2/17:ℚ),(63/34:ℚ),(-33/34:ℚ),(-33/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/34:ℚ),(-13/34:ℚ),(25/17:ℚ),(-40/17:ℚ),(41/34:ℚ),(1/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/17:ℚ),(-10/17:ℚ),(1/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n3]
  all_goals ring
def num004 : List ℚ := [(1/68:ℚ),(-13/68:ℚ),(71/68:ℚ),(-233/68:ℚ),(487/68:ℚ),(-671/68:ℚ),(593/68:ℚ),(-299/68:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n4]
  all_goals ring
def num005 : List ℚ := [(1/34:ℚ),(-9/34:ℚ),(27/34:ℚ),(-10/17:ℚ),(-61/34:ℚ),(161/34:ℚ),(-147/34:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n5]
  all_goals ring
def num006 : List ℚ := [(-1/34:ℚ),(7/17:ℚ),(-32/17:ℚ),(71/17:ℚ),(-159/34:ℚ),(2/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n6]
  all_goals ring
def num007 : List ℚ := [(1/68:ℚ),(-4/17:ℚ),(5/4:ℚ),(-56/17:ℚ),(363/68:ℚ),(-96/17:ℚ),(239/68:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/17:ℚ),(7/17:ℚ),(-10/17:ℚ),(-21/17:ℚ),(49/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n8]
  all_goals ring
def num009 : List ℚ := [(-1/34:ℚ),(7/17:ℚ),(-31/17:ℚ),(59/17:ℚ),(-5/2:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-3/34:ℚ),(8/17:ℚ),(-5/17:ℚ),(-24/17:ℚ),(77/34:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n10]
  all_goals ring
def num011 : List ℚ := [(-1/34:ℚ),(1/17:ℚ),(9/17:ℚ),(-43/17:ℚ),(115/34:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.n11]
  all_goals ring
def denominator : List ℚ := [(1/17:ℚ),(-10/17:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even033.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even033.den,Blueprint.Thomson.Finite.RFCatalogue.rf1064]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even033.PairData
