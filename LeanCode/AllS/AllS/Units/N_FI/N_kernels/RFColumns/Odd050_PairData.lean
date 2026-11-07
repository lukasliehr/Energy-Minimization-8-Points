import AllS.Units.N_FI.N_kernels.RFColumns.Odd050_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd050.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/40:ℚ),(5/14:ℚ),(-53/28:ℚ),(279/70:ℚ),(48/35:ℚ),(-1431/70:ℚ),(4061/140:ℚ),(-417/70:ℚ),(-311/40:ℚ),(16/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n0]
  all_goals ring
def num001 : List ℚ := [(-3/280:ℚ),(39/280:ℚ),(-22/35:ℚ),(32/35:ℚ),(197/140:ℚ),(-173/28:ℚ),(36/5:ℚ),(-24/7:ℚ),(41/280:ℚ),(379/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n1]
  all_goals ring
def num002 : List ℚ := [(-3/280:ℚ),(1/7:ℚ),(-87/140:ℚ),(22/35:ℚ),(21/10:ℚ),(-156/35:ℚ),(11/140:ℚ),(17/7:ℚ),(5/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n2]
  all_goals ring
def num003 : List ℚ := [(1/280:ℚ),(-13/280:ℚ),(11/35:ℚ),(-111/70:ℚ),(137/28:ℚ),(-667/140:ℚ),(-77/5:ℚ),(3247/70:ℚ),(-9659/280:ℚ),(547/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(3/70:ℚ),(-33/70:ℚ),(113/70:ℚ),(-9/10:ℚ),(-407/70:ℚ),(853/70:ℚ),(-717/70:ℚ),(379/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n4]
  all_goals ring
def num005 : List ℚ := [(-1/70:ℚ),(13/70:ℚ),(-29/35:ℚ),(8/7:ℚ),(19/10:ℚ),(-93/14:ℚ),(111/35:ℚ),(2/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n5]
  all_goals ring
def num006 : List ℚ := [(3/280:ℚ),(-1/14:ℚ),(-5/28:ℚ),(153/70:ℚ),(-281/70:ℚ),(-309/70:ℚ),(2789/140:ℚ),(-1223/70:ℚ),(361/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n6]
  all_goals ring
def num007 : List ℚ := [(3/140:ℚ),(-33/140:ℚ),(111/140:ℚ),(-9/28:ℚ),(-443/140:ℚ),(809/140:ℚ),(-583/140:ℚ),(309/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n7]
  all_goals ring
def num008 : List ℚ := [(1/140:ℚ),(-9/140:ℚ),(13/140:ℚ),(59/140:ℚ),(-97/140:ℚ),(-127/140:ℚ),(67/140:ℚ),(-1/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd050.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd050.den,Blueprint.Thomson.Finite.RFCatalogue.rf1934]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd050.PairData
