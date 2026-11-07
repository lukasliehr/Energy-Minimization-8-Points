import AllS.Units.N_FI.N_kernels.RFColumns.Odd025_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd025.PairData
def num000 : List ℚ := [(-1/280:ℚ),(3/56:ℚ),(-17/40:ℚ),(881/280:ℚ),(-3039/140:ℚ),(14983/140:ℚ),(-47237/140:ℚ),(2583/4:ℚ),(-186097/280:ℚ),(7221/40:ℚ),(81393/280:ℚ),(-9437/40:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n0]
  all_goals ring
def num001 : List ℚ := [(3/280:ℚ),(-39/140:ℚ),(839/280:ℚ),(-634/35:ℚ),(9559/140:ℚ),(-11579/70:ℚ),(35379/140:ℚ),(-7804/35:ℚ),(22719/280:ℚ),(3349/140:ℚ),(-891/40:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n1]
  all_goals ring
def num002 : List ℚ := [(1/70:ℚ),(-2/7:ℚ),(171/70:ℚ),(-57/5:ℚ),(409/14:ℚ),(-976/35:ℚ),(-3791/70:ℚ),(1389/7:ℚ),(-1187/5:ℚ),(112/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n2]
  all_goals ring
def num003 : List ℚ := [(3/140:ℚ),(-33/70:ℚ),(123/28:ℚ),(-219/10:ℚ),(4001/70:ℚ),(-415/14:ℚ),(-21853/70:ℚ),(80033/70:ℚ),(-272717/140:ℚ),(61508/35:ℚ),(-14099/20:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-3/70:ℚ),(36/35:ℚ),(-349/35:ℚ),(268/5:ℚ),(-6178/35:ℚ),(12764/35:ℚ),(-16183/35:ℚ),(11644/35:ℚ),(-1031/10:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n4]
  all_goals ring
def num005 : List ℚ := [(-1/70:ℚ),(3/10:ℚ),(-87/35:ℚ),(141/14:ℚ),(-91/5:ℚ),(-209/70:ℚ),(2453/35:ℚ),(-1123/10:ℚ),(133/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(19/140:ℚ),(-26/35:ℚ),(-9/10:ℚ),(2019/70:ℚ),(-753/5:ℚ),(14228/35:ℚ),(-1255/2:ℚ),(75059/140:ℚ),(-4057/20:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n6]
  all_goals ring
def num007 : List ℚ := [(-3/140:ℚ),(18/35:ℚ),(-349/70:ℚ),(134/5:ℚ),(-3089/35:ℚ),(6382/35:ℚ),(-16183/70:ℚ),(5822/35:ℚ),(-1031/20:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n7]
  all_goals ring
def num008 : List ℚ := [(-1/35:ℚ),(37/70:ℚ),(-136/35:ℚ),(981/70:ℚ),(-153/7:ℚ),(-149/14:ℚ),(3354/35:ℚ),(-9729/70:ℚ),(76/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd025.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd025.den,Blueprint.Thomson.Finite.RFCatalogue.rf1524]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd025.PairData
