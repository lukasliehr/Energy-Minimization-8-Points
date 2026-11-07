import AllS.Units.N_FI.N_kernels.RFColumns.Odd043_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd043.PairData
def num000 : List ℚ := [(0/1:ℚ),(-41/280:ℚ),(221/140:ℚ),(-691/140:ℚ),(-387/140:ℚ),(264/5:ℚ),(-2719/20:ℚ),(22779/140:ℚ),(-11337/140:ℚ),(-5927/280:ℚ),(754/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n0]
  all_goals ring
def num001 : List ℚ := [(-17/280:ℚ),(159/280:ℚ),(-23/20:ℚ),(-559/140:ℚ),(852/35:ℚ),(-3889/70:ℚ),(9853/140:ℚ),(-6229/140:ℚ),(-1/40:ℚ),(3821/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n1]
  all_goals ring
def num002 : List ℚ := [(-17/280:ℚ),(87/140:ℚ),(-237/140:ℚ),(-89/140:ℚ),(479/70:ℚ),(-101/20:ℚ),(-37/20:ℚ),(19/20:ℚ),(7/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n2]
  all_goals ring
def num003 : List ℚ := [(1/40:ℚ),(-73/280:ℚ),(201/140:ℚ),(-821/140:ℚ),(59/7:ℚ),(443/14:ℚ),(-21649/140:ℚ),(38181/140:ℚ),(-69679/280:ℚ),(24653/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(17/70:ℚ),(-25/14:ℚ),(87/70:ℚ),(1189/70:ℚ),(-885/14:ℚ),(7941/70:ℚ),(-8063/70:ℚ),(3891/70:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n4]
  all_goals ring
def num005 : List ℚ := [(-3/35:ℚ),(9/10:ℚ),(-92/35:ℚ),(-3/14:ℚ),(69/7:ℚ),(-703/70:ℚ),(-2/7:ℚ),(5/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n5]
  all_goals ring
def num006 : List ℚ := [(17/280:ℚ),(-1/4:ℚ),(-183/140:ℚ),(669/140:ℚ),(803/70:ℚ),(-9537/140:ℚ),(17767/140:ℚ),(-16441/140:ℚ),(14339/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n6]
  all_goals ring
def num007 : List ℚ := [(17/140:ℚ),(-25/28:ℚ),(87/140:ℚ),(1189/140:ℚ),(-885/28:ℚ),(7941/140:ℚ),(-8063/140:ℚ),(3891/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n7]
  all_goals ring
def num008 : List ℚ := [(1/28:ℚ),(-33/140:ℚ),(-11/140:ℚ),(41/20:ℚ),(-3/4:ℚ),(-459/140:ℚ),(163/28:ℚ),(15/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-1/5:ℚ),(3/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd043.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd043.den,Blueprint.Thomson.Finite.RFCatalogue.rf1927]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd043.PairData
