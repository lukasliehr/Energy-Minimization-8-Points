import AllS.Units.N_FI.N_kernels.RFColumns.Odd047_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd047.PairData
def num000 : List ℚ := [(0/1:ℚ),(17/280:ℚ),(-53/70:ℚ),(93/28:ℚ),(-27/5:ℚ),(-41/35:ℚ),(507/70:ℚ),(341/20:ℚ),(-1482/35:ℚ),(3439/280:ℚ),(468/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n0]
  all_goals ring
def num001 : List ℚ := [(1/40:ℚ),(-11/40:ℚ),(67/70:ℚ),(-31/35:ℚ),(-13/28:ℚ),(-603/140:ℚ),(249/14:ℚ),(-641/35:ℚ),(187/280:ℚ),(1347/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n1]
  all_goals ring
def num002 : List ℚ := [(1/40:ℚ),(-2/7:ℚ),(27/28:ℚ),(-3/14:ℚ),(-136/35:ℚ),(157/35:ℚ),(41/28:ℚ),(-27/14:ℚ),(-5/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n2]
  all_goals ring
def num003 : List ℚ := [(-3/280:ℚ),(37/280:ℚ),(-57/70:ℚ),(69/20:ℚ),(-1089/140:ℚ),(88/35:ℚ),(223/14:ℚ),(19/20:ℚ),(-16707/280:ℚ),(14731/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-13/140:ℚ),(23/28:ℚ),(-261/140:ℚ),(3/140:ℚ),(-79/140:ℚ),(2657/140:ℚ),(-5151/140:ℚ),(2729/140:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n4]
  all_goals ring
def num005 : List ℚ := [(1/28:ℚ),(-3/7:ℚ),(223/140:ℚ),(-67/70:ℚ),(-153/28:ℚ),(304/35:ℚ),(-27/28:ℚ),(-5/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n5]
  all_goals ring
def num006 : List ℚ := [(-1/40:ℚ),(19/140:ℚ),(33/70:ℚ),(-499/140:ℚ),(87/20:ℚ),(157/140:ℚ),(603/70:ℚ),(-4349/140:ℚ),(6613/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n6]
  all_goals ring
def num007 : List ℚ := [(-1/20:ℚ),(9/20:ℚ),(-149/140:ℚ),(13/140:ℚ),(1/20:ℚ),(1233/140:ℚ),(-2507/140:ℚ),(1347/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n7]
  all_goals ring
def num008 : List ℚ := [(-1/70:ℚ),(3/28:ℚ),(-1/70:ℚ),(-149/140:ℚ),(7/10:ℚ),(81/28:ℚ),(-19/14:ℚ),(-5/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd047.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd047.den,Blueprint.Thomson.Finite.RFCatalogue.rf1931]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd047.PairData
