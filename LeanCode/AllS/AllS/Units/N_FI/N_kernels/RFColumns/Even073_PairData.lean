import AllS.Units.N_FI.N_kernels.RFColumns.Even073_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even073.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/238:ℚ),(-9/119:ℚ),(127/238:ℚ),(-235/119:ℚ),(450/119:ℚ),(-130/119:ℚ),(-68/7:ℚ),(1954/119:ℚ),(-3341/238:ℚ),(3811/119:ℚ),(-8943/238:ℚ),(-1679/119:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(1/476:ℚ),(-13/476:ℚ),(37/238:ℚ),(-67/119:ℚ),(249/238:ℚ),(311/238:ℚ),(-1062/119:ℚ),(109/17:ℚ),(9309/476:ℚ),(-6529/476:ℚ),(-983/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-3/238:ℚ),(3/14:ℚ),(-150/119:ℚ),(363/119:ℚ),(-157/119:ℚ),(-914/119:ℚ),(1674/119:ℚ),(-1563/119:ℚ),(2965/238:ℚ),(1/14:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-3/119:ℚ),(40/119:ℚ),(-155/119:ℚ),(216/119:ℚ),(-9/119:ℚ),(-64/7:ℚ),(17/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n3]
  all_goals ring
def num004 : List ℚ := [(-1/238:ℚ),(10/119:ℚ),(-82/119:ℚ),(729/238:ℚ),(-54/7:ℚ),(1010/119:ℚ),(1107/119:ℚ),(-5665/119:ℚ),(15965/238:ℚ),(-4832/119:ℚ),(481/17:ℚ),(-12879/238:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n4]
  all_goals ring
def num005 : List ℚ := [(-1/476:ℚ),(13/476:ℚ),(-69/476:ℚ),(46/119:ℚ),(-6/17:ℚ),(-319/238:ℚ),(856/119:ℚ),(-1844/119:ℚ),(1985/476:ℚ),(3055/68:ℚ),(-4725/68:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n5]
  all_goals ring
def num006 : List ℚ := [(3/238:ℚ),(-55/238:ℚ),(185/119:ℚ),(-34/7:ℚ),(100/17:ℚ),(743/119:ℚ),(-3441/119:ℚ),(4302/119:ℚ),(-861/34:ℚ),(193/14:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n6]
  all_goals ring
def num007 : List ℚ := [(-1/119:ℚ),(19/119:ℚ),(-135/119:ℚ),(67/17:ℚ),(-808/119:ℚ),(331/119:ℚ),(244/17:ℚ),(-5529/119:ℚ),(8697/119:ℚ),(-5402/119:ℚ),(1675/119:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(1/238:ℚ),(-11/238:ℚ),(41/238:ℚ),(-33/238:ℚ),(-87/238:ℚ),(59/238:ℚ),(-63/34:ℚ),(167/34:ℚ),(133/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n8]
  all_goals ring
def num009 : List ℚ := [(2/119:ℚ),(-5/17:ℚ),(31/17:ℚ),(-583/119:ℚ),(421/119:ℚ),(1383/119:ℚ),(-3613/119:ℚ),(3363/119:ℚ),(-83/7:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n9]
  all_goals ring
def num010 : List ℚ := [(-1/238:ℚ),(19/238:ℚ),(-57/119:ℚ),(104/119:ℚ),(174/119:ℚ),(-789/119:ℚ),(457/119:ℚ),(108/17:ℚ),(-1531/238:ℚ),(617/34:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n10]
  all_goals ring
def num011 : List ℚ := [(1/476:ℚ),(-3/238:ℚ),(1/119:ℚ),(1/14:ℚ),(-5/14:ℚ),(463/238:ℚ),(-579/119:ℚ),(-989/238:ℚ),(1671/68:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even073.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even073.den,Blueprint.Thomson.Finite.RFCatalogue.rf1665]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even073.PairData
