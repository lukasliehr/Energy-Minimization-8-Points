import AllS.Units.N_FI.N_kernels.RFColumns.Odd037_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd037.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-33/140:ℚ),(10/7:ℚ),(-17/5:ℚ),(-11/35:ℚ),(927/70:ℚ),(-386/35:ℚ),(-401/35:ℚ),(829/70:ℚ),(-123/20:ℚ),(-172/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n0]
  all_goals ring
def num001 : List ℚ := [(1/140:ℚ),(-1/10:ℚ),(67/140:ℚ),(-51/70:ℚ),(-57/70:ℚ),(39/14:ℚ),(-1/70:ℚ),(-321/70:ℚ),(633/140:ℚ),(-12/35:ℚ),(-169/140:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n1]
  all_goals ring
def num002 : List ℚ := [(1/140:ℚ),(-3/35:ℚ),(2/7:ℚ),(4/35:ℚ),(-121/70:ℚ),(32/35:ℚ),(74/35:ℚ),(-4/5:ℚ),(257/140:ℚ),(1/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-37/140:ℚ),(9/5:ℚ),(-181/35:ℚ),(14/5:ℚ),(33/2:ℚ),(-195/7:ℚ),(-167/35:ℚ),(239/14:ℚ),(-2577/140:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-1/35:ℚ),(11/35:ℚ),(-33/35:ℚ),(-9/35:ℚ),(127/35:ℚ),(9/35:ℚ),(-263/35:ℚ),(293/35:ℚ),(-134/35:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n4]
  all_goals ring
def num005 : List ℚ := [(-1/140:ℚ),(2/35:ℚ),(0/1:ℚ),(-24/35:ℚ),(1/14:ℚ),(118/35:ℚ),(4/7:ℚ),(-104/35:ℚ),(13/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n5]
  all_goals ring
def num006 : List ℚ := [(-1/140:ℚ),(1/14:ℚ),(-9/70:ℚ),(-39/70:ℚ),(7/5:ℚ),(61/70:ℚ),(17/70:ℚ),(-473/70:ℚ),(169/28:ℚ),(-169/35:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n6]
  all_goals ring
def num007 : List ℚ := [(-1/70:ℚ),(13/70:ℚ),(-11/14:ℚ),(69/70:ℚ),(9/14:ℚ),(-3/2:ℚ),(207/70:ℚ),(-249/70:ℚ),(38/35:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n7]
  all_goals ring
def num008 : List ℚ := [(1/140:ℚ),(-4/35:ℚ),(23/35:ℚ),(-44/35:ℚ),(-17/10:ℚ),(256/35:ℚ),(-11/7:ℚ),(-24/7:ℚ),(15/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd037.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd037.den,Blueprint.Thomson.Finite.RFCatalogue.rf1536]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd037.PairData
