import AllS.Units.N_FI.N_kernels.RFColumns.Odd055_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd055.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/280:ℚ),(-19/280:ℚ),(1/2:ℚ),(-117/70:ℚ),(261/140:ℚ),(321/140:ℚ),(-95/14:ℚ),(633/70:ℚ),(-3131/280:ℚ),(-447/280:ℚ),(74/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n0]
  all_goals ring
def num001 : List ℚ := [(1/280:ℚ),(-2/35:ℚ),(93/280:ℚ),(-11/14:ℚ),(43/140:ℚ),(111/70:ℚ),(-393/140:ℚ),(243/70:ℚ),(-871/280:ℚ),(9/70:ℚ),(261/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n1]
  all_goals ring
def num002 : List ℚ := [(1/280:ℚ),(-3/56:ℚ),(19/70:ℚ),(-31/70:ℚ),(-51/140:ℚ),(45/28:ℚ),(-143/70:ℚ),(139/70:ℚ),(277/280:ℚ),(-1/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n2]
  all_goals ring
def num003 : List ℚ := [(1/280:ℚ),(-2/35:ℚ),(89/280:ℚ),(-39/70:ℚ),(-167/140:ℚ),(437/70:ℚ),(-1023/140:ℚ),(-257/70:ℚ),(841/56:ℚ),(-1769/70:ℚ),(2053/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/70:ℚ),(1/5:ℚ),(-34/35:ℚ),(61/35:ℚ),(1/35:ℚ),(-139/35:ℚ),(58/7:ℚ),(-281/35:ℚ),(191/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-1/70:ℚ),(3/14:ℚ),(-69/70:ℚ),(67/70:ℚ),(193/70:ℚ),(-319/70:ℚ),(277/70:ℚ),(-1/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n5]
  all_goals ring
def num006 : List ℚ := [(-1/280:ℚ),(1/40:ℚ),(9/70:ℚ),(-109/70:ℚ),(17/4:ℚ),(-193/140:ℚ),(-107/10:ℚ),(1321/70:ℚ),(-3029/280:ℚ),(-181/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n6]
  all_goals ring
def num007 : List ℚ := [(-1/140:ℚ),(1/10:ℚ),(-16/35:ℚ),(41/70:ℚ),(59/70:ℚ),(-163/70:ℚ),(76/35:ℚ),(51/70:ℚ),(-229/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n7]
  all_goals ring
def num008 : List ℚ := [(-1/140:ℚ),(1/10:ℚ),(-33/70:ℚ),(51/70:ℚ),(22/35:ℚ),(-263/70:ℚ),(377/70:ℚ),(173/70:ℚ),(-13/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.n8]
  all_goals ring
def denominator : List ℚ := [(-1/35:ℚ),(8/35:ℚ),(-2/7:ℚ),(-32/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd055.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd055.den,Blueprint.Thomson.Finite.RFCatalogue.rf1939]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd055.PairData
