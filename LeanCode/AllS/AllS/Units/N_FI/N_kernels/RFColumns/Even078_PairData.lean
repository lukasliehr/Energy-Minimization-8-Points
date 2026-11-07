import AllS.Units.N_FI.N_kernels.RFColumns.Even078_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even078.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/136:ℚ),(7/68:ℚ),(-45/68:ℚ),(95/34:ℚ),(-283/34:ℚ),(575/34:ℚ),(-1467/68:ℚ),(471/34:ℚ),(-3/136:ℚ),(-273/68:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/68:ℚ),(9/68:ℚ),(-21/68:ℚ),(-77/68:ℚ),(579/68:ℚ),(-1393/68:ℚ),(1393/68:ℚ),(-147/68:ℚ),(-251/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/68:ℚ),(-1/4:ℚ),(107/68:ℚ),(-343/68:ℚ),(587/68:ℚ),(-471/68:ℚ),(49/68:ℚ),(7/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/17:ℚ),(-10/17:ℚ),(1/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n3]
  all_goals ring
def num004 : List ℚ := [(1/136:ℚ),(-15/136:ℚ),(14/17:ℚ),(-275/68:ℚ),(909/68:ℚ),(-1023/34:ℚ),(793/17:ℚ),(-3373/68:ℚ),(4621/136:ℚ),(-1621/136:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n4]
  all_goals ring
def num005 : List ℚ := [(1/68:ℚ),(-9/68:ℚ),(13/34:ℚ),(35/68:ℚ),(-122/17:ℚ),(1653/68:ℚ),(-1503/34:ℚ),(3049/68:ℚ),(-1421/68:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n5]
  all_goals ring
def num006 : List ℚ := [(-1/68:ℚ),(9/34:ℚ),(-127/68:ℚ),(123/17:ℚ),(-1123/68:ℚ),(751/34:ℚ),(-1101/68:ℚ),(5/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n6]
  all_goals ring
def num007 : List ℚ := [(1/136:ℚ),(-11/68:ℚ),(45/34:ℚ),(-385/68:ℚ),(1011/68:ℚ),(-1765/68:ℚ),(1057/34:ℚ),(-1647/68:ℚ),(1313/136:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/17:ℚ),(21/34:ℚ),(-71/34:ℚ),(23/17:ℚ),(129/17:ℚ),(-623/34:ℚ),(451/34:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n8]
  all_goals ring
def num009 : List ℚ := [(-1/68:ℚ),(5/17:ℚ),(-149/68:ℚ),(134/17:ℚ),(-1031/68:ℚ),(263/17:ℚ),(-27/4:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n9]
  all_goals ring
def num010 : List ℚ := [(0/1:ℚ),(-5/68:ℚ),(21/34:ℚ),(-115/68:ℚ),(15/17:ℚ),(317/68:ℚ),(-331/34:ℚ),(427/68:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n10]
  all_goals ring
def num011 : List ℚ := [(-1/68:ℚ),(0/1:ℚ),(3/4:ℚ),(-88/17:ℚ),(1097/68:ℚ),(-414/17:ℚ),(1021/68:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.n11]
  all_goals ring
def denominator : List ℚ := [(1/17:ℚ),(-10/17:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even078.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even078.den,Blueprint.Thomson.Finite.RFCatalogue.rf1670]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even078.PairData
