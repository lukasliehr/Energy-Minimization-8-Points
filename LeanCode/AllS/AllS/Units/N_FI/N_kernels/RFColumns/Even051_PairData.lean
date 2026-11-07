import AllS.Units.N_FI.N_kernels.RFColumns.Even051_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even051.PairData
def num000 : List ℚ := [(0/1:ℚ),(-1/476:ℚ),(1/28:ℚ),(-53/238:ℚ),(82/119:ℚ),(-211/238:ℚ),(-487/238:ℚ),(1418/119:ℚ),(-2552/119:ℚ),(5487/476:ℚ),(3285/476:ℚ),(-515/238:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-2/119:ℚ),(31/119:ℚ),(-157/119:ℚ),(256/119:ℚ),(316/119:ℚ),(-207/17:ℚ),(835/119:ℚ),(134/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/119:ℚ),(-16/119:ℚ),(82/119:ℚ),(-123/119:ℚ),(-271/119:ℚ),(1154/119:ℚ),(-1112/119:ℚ),(-183/119:ℚ),(20/7:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(1/119:ℚ),(-9/119:ℚ),(-6/119:ℚ),(18/17:ℚ),(-11/119:ℚ),(-3/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n3]
  all_goals ring
def num004 : List ℚ := [(1/476:ℚ),(-19/476:ℚ),(141/476:ℚ),(-20/17:ℚ),(321/119:ℚ),(-633/238:ℚ),(-82/17:ℚ),(2976/119:ℚ),(-21365/476:ℚ),(16757/476:ℚ),(-1509/476:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-1/119:ℚ),(4/17:ℚ),(-207/119:ℚ),(536/119:ℚ),(-39/119:ℚ),(-284/17:ℚ),(385/17:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n5]
  all_goals ring
def num006 : List ℚ := [(-1/119:ℚ),(1/7:ℚ),(-101/119:ℚ),(256/119:ℚ),(-146/119:ℚ),(-767/119:ℚ),(2059/119:ℚ),(-2082/119:ℚ),(45/7:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n6]
  all_goals ring
def num007 : List ℚ := [(1/238:ℚ),(-9/119:ℚ),(117/238:ℚ),(-347/238:ℚ),(431/238:ℚ),(1/238:ℚ),(-417/238:ℚ),(1111/238:ℚ),(-1762/119:ℚ),(2645/238:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(3/119:ℚ),(-41/119:ℚ),(134/119:ℚ),(54/119:ℚ),(-79/17:ℚ),(21/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n8]
  all_goals ring
def num009 : List ℚ := [(-1/119:ℚ),(1/7:ℚ),(-99/119:ℚ),(229/119:ℚ),(-9/17:ℚ),(-589/119:ℚ),(787/119:ℚ),(-9/7:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n9]
  all_goals ring
def num010 : List ℚ := [(1/476:ℚ),(-9/238:ℚ),(26/119:ℚ),(-71/238:ℚ),(-321/238:ℚ),(1049/238:ℚ),(-46/119:ℚ),(-153/14:ℚ),(423/68:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(2/119:ℚ),(-40/119:ℚ),(156/119:ℚ),(8/17:ℚ),(-98/17:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even051.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even051.den,Blueprint.Thomson.Finite.RFCatalogue.rf1322]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even051.PairData
