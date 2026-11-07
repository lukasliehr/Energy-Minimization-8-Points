import AllS.Units.N_FI.N_kernels.RFColumns.Even066_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even066.PairData
def num000 : List ℚ := [(0/1:ℚ),(3/136:ℚ),(-30/119:ℚ),(407/952:ℚ),(857/476:ℚ),(395/68:ℚ),(-9476/119:ℚ),(119451/476:ℚ),(-81563/238:ℚ),(25729/952:ℚ),(67140/119:ℚ),(-517117/952:ℚ),(-11453/68:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(25/476:ℚ),(-363/476:ℚ),(405/119:ℚ),(-95/34:ℚ),(-2392/119:ℚ),(6738/119:ℚ),(-215/34:ℚ),(-38135/238:ℚ),(95927/476:ℚ),(5221/68:ℚ),(-11767/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-5/68:ℚ),(83/68:ℚ),(-1759/238:ℚ),(5779/238:ℚ),(-6535/119:ℚ),(7858/119:ℚ),(2543/238:ℚ),(-37307/238:ℚ),(99103/476:ℚ),(-107/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-1/17:ℚ),(6/7:ℚ),(-538/119:ℚ),(258/17:ℚ),(-4184/119:ℚ),(1650/119:ℚ),(13082/119:ℚ),(-4074/17:ℚ),(217/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n3]
  all_goals ring
def num004 : List ℚ := [(-3/136:ℚ),(55/136:ℚ),(-2627/952:ℚ),(8013/952:ℚ),(-507/68:ℚ),(-8707/476:ℚ),(8633/476:ℚ),(69469/476:ℚ),(-446017/952:ℚ),(462949/952:ℚ),(125921/952:ℚ),(-92705/136:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n4]
  all_goals ring
def num005 : List ℚ := [(-1/476:ℚ),(11/476:ℚ),(-137/476:ℚ),(159/238:ℚ),(1264/119:ℚ),(-8571/119:ℚ),(20288/119:ℚ),(-2833/34:ℚ),(-214199/476:ℚ),(479377/476:ℚ),(-57801/68:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n5]
  all_goals ring
def num006 : List ℚ := [(5/68:ℚ),(-41/34:ℚ),(788/119:ℚ),(-1803/119:ℚ),(4007/238:ℚ),(-1786/119:ℚ),(294/17:ℚ),(-1165/119:ℚ),(-25961/476:ℚ),(213/2:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n6]
  all_goals ring
def num007 : List ℚ := [(-7/136:ℚ),(15/17:ℚ),(-747/136:ℚ),(2049/119:ℚ),(-13837/476:ℚ),(-29/7:ℚ),(73603/476:ℚ),(-46077/119:ℚ),(492267/952:ℚ),(-29856/119:ℚ),(8769/136:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-5/119:ℚ),(107/238:ℚ),(151/238:ℚ),(-3649/238:ℚ),(9287/238:ℚ),(-2447/238:ℚ),(-23291/238:ℚ),(7411/34:ℚ),(-2527/34:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n8]
  all_goals ring
def num009 : List ℚ := [(7/68:ℚ),(-55/34:ℚ),(1899/238:ℚ),(-2865/238:ℚ),(-1608/119:ℚ),(19413/238:ℚ),(-36115/238:ℚ),(33821/238:ℚ),(-263/4:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n9]
  all_goals ring
def num010 : List ℚ := [(-1/34:ℚ),(33/68:ℚ),(-43/17:ℚ),(592/119:ℚ),(-184/119:ℚ),(-3973/238:ℚ),(6373/119:ℚ),(-5570/119:ℚ),(-1977/238:ℚ),(13437/68:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n10]
  all_goals ring
def num011 : List ℚ := [(1/476:ℚ),(-1/238:ℚ),(33/238:ℚ),(355/238:ℚ),(-297/17:ℚ),(509/14:ℚ),(3399/238:ℚ),(-3609/34:ℚ),(13629/68:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even066.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even066.den,Blueprint.Thomson.Finite.RFCatalogue.rf1658]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even066.PairData
