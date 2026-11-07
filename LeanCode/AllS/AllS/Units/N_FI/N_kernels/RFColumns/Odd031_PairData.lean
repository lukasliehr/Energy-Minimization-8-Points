import AllS.Units.N_FI.N_kernels.RFColumns.Odd031_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd031.PairData
def num000 : List ℚ := [(0/1:ℚ),(5/7:ℚ),(-73/14:ℚ),(93/7:ℚ),(-155/14:ℚ),(-19/7:ℚ),(3/2:ℚ),(17/7:ℚ),(15/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n0]
  all_goals ring
def num001 : List ℚ := [(2/7:ℚ),(-47/28:ℚ),(45/14:ℚ),(-107/28:ℚ),(67/7:ℚ),(-461/28:ℚ),(97/14:ℚ),(183/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n1]
  all_goals ring
def num002 : List ℚ := [(2/7:ℚ),(-12/7:ℚ),(10/7:ℚ),(40/7:ℚ),(-58/7:ℚ),(4/7:ℚ),(2/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n2]
  all_goals ring
def num003 : List ℚ := [(-1/7:ℚ),(13/14:ℚ),(-32/7:ℚ),(209/14:ℚ),(-131/7:ℚ),(-29/14:ℚ),(20/7:ℚ),(95/14:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n3]
  all_goals ring
def num004 : List ℚ := [(-1/28:ℚ),(-13/14:ℚ),(117/28:ℚ),(-39/7:ℚ),(297/28:ℚ),(-51/2:ℚ),(739/28:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n4]
  all_goals ring
def num005 : List ℚ := [(3/7:ℚ),(-19/7:ℚ),(22/7:ℚ),(50/7:ℚ),(-15/1:ℚ),(7/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n5]
  all_goals ring
def num006 : List ℚ := [(-2/7:ℚ),(0/1:ℚ),(43/7:ℚ),(-90/7:ℚ),(66/7:ℚ),(-102/7:ℚ),(85/7:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n6]
  all_goals ring
def num007 : List ℚ := [(-4/7:ℚ),(31/14:ℚ),(-18/7:ℚ),(33/7:ℚ),(-86/7:ℚ),(183/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n7]
  all_goals ring
def num008 : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(12/7:ℚ),(-2/1:ℚ),(-27/7:ℚ),(4/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd031.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd031.den,Blueprint.Thomson.Finite.RFCatalogue.rf1530]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd031.PairData
