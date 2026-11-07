import AllS.Units.N_FI.N_kernels.RFColumns.Odd046_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd046.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-13/70:ℚ),(9/10:ℚ),(-137/70:ℚ),(25/14:ℚ),(-143/70:ℚ),(513/70:ℚ),(-439/70:ℚ),(-167/35:ℚ),(-2/7:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-3/35:ℚ),(5/14:ℚ),(-3/5:ℚ),(3/5:ℚ),(-11/5:ℚ),(53/10:ℚ),(-129/35:ℚ),(-11/20:ℚ),(6/7:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-3/35:ℚ),(11/35:ℚ),(-6/35:ℚ),(-69/70:ℚ),(43/35:ℚ),(-19/35:ℚ),(46/35:ℚ),(3/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-1/140:ℚ),(1/28:ℚ),(5/28:ℚ),(-197/140:ℚ),(63/20:ℚ),(-145/28:ℚ),(395/28:ℚ),(-2923/140:ℚ),(6/7:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(2/7:ℚ),(-32/35:ℚ),(41/35:ℚ),(-69/35:ℚ),(216/35:ℚ),(-50/7:ℚ),(17/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n4]
  all_goals ring
def num005 : List ℚ := [(1/140:ℚ),(-11/140:ℚ),(33/140:ℚ),(17/140:ℚ),(-37/28:ℚ),(59/140:ℚ),(59/28:ℚ),(5/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(3/70:ℚ),(4/35:ℚ),(-11/10:ℚ),(131/70:ℚ),(-23/14:ℚ),(216/35:ℚ),(-627/70:ℚ),(47/28:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(1/7:ℚ),(-31/70:ℚ),(16/35:ℚ),(-51/70:ℚ),(17/5:ℚ),(-317/70:ℚ),(12/7:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n7]
  all_goals ring
def num008 : List ℚ := [(-1/140:ℚ),(9/140:ℚ),(-3/28:ℚ),(-41/140:ℚ),(13/28:ℚ),(11/28:ℚ),(79/140:ℚ),(3/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd046.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd046.den,Blueprint.Thomson.Finite.RFCatalogue.rf1930]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd046.PairData
