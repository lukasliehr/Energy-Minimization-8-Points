import AllS.Units.N_FI.N_kernels.RFColumns.Even041_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even041.PairData
def num000 : List ℚ := [(0/1:ℚ),(31/238:ℚ),(-57/28:ℚ),(2357/238:ℚ),(-144/17:ℚ),(-9084/119:ℚ),(71307/238:ℚ),(-53826/119:ℚ),(14718/119:ℚ),(128897/238:ℚ),(-265989/476:ℚ),(-5471/34:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n0]
  all_goals ring
def num001 : List ℚ := [(6/119:ℚ),(-349/476:ℚ),(386/119:ℚ),(-569/238:ℚ),(-4863/238:ℚ),(6653/119:ℚ),(-117/34:ℚ),(-39359/238:ℚ),(6849/34:ℚ),(40281/476:ℚ),(-11635/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(5/68:ℚ),(-401/238:ℚ),(3567/238:ℚ),(-14785/238:ℚ),(12639/119:ℚ),(-8027/238:ℚ),(-34143/238:ℚ),(51053/238:ℚ),(-121/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n2]
  all_goals ring
def num003 : List ℚ := [(-1/17:ℚ),(6/7:ℚ),(-538/119:ℚ),(258/17:ℚ),(-4184/119:ℚ),(1650/119:ℚ),(13082/119:ℚ),(-4074/17:ℚ),(217/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n3]
  all_goals ring
def num004 : List ℚ := [(-1/34:ℚ),(4/7:ℚ),(-2269/476:ℚ),(341/17:ℚ),(-4443/119:ℚ),(-3517/119:ℚ),(73119/238:ℚ),(-84719/119:ℚ),(166881/238:ℚ),(3253/119:ℚ),(-44879/68:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n4]
  all_goals ring
def num005 : List ℚ := [(-3/476:ℚ),(-59/476:ℚ),(55/238:ℚ),(2627/238:ℚ),(-8490/119:ℚ),(19920/119:ℚ),(-18503/238:ℚ),(-107683/238:ℚ),(68253/68:ℚ),(-57043/68:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n5]
  all_goals ring
def num006 : List ℚ := [(3/68:ℚ),(-87/119:ℚ),(332/119:ℚ),(53/7:ℚ),(-13967/238:ℚ),(2029/17:ℚ),(-12890/119:ℚ),(-57/7:ℚ),(391/4:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n6]
  all_goals ring
def num007 : List ℚ := [(-1/68:ℚ),(1/17:ℚ),(208/119:ℚ),(-1389/119:ℚ),(1765/238:ℚ),(9257/119:ℚ),(-28990/119:ℚ),(44057/119:ℚ),(-81547/476:ℚ),(796/17:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n7]
  all_goals ring
def num008 : List ℚ := [(-3/68:ℚ),(111/238:ℚ),(141/238:ℚ),(-3645/238:ℚ),(4656/119:ℚ),(-21/2:ℚ),(-22989/238:ℚ),(7335/34:ℚ),(-5565/68:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n8]
  all_goals ring
def num009 : List ℚ := [(1/34:ℚ),(-159/238:ℚ),(1055/238:ℚ),(-2383/238:ℚ),(5693/238:ℚ),(-15829/238:ℚ),(21277/238:ℚ),(-107/2:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n9]
  all_goals ring
def num010 : List ℚ := [(1/68:ℚ),(-5/17:ℚ),(396/119:ℚ),(-1675/119:ℚ),(2019/238:ℚ),(6751/119:ℚ),(-10974/119:ℚ),(3887/119:ℚ),(12653/68:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n10]
  all_goals ring
def num011 : List ℚ := [(3/238:ℚ),(23/238:ℚ),(359/238:ℚ),(-4133/238:ℚ),(8601/238:ℚ),(3701/238:ℚ),(-3685/34:ℚ),(6559/34:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even041.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even041.den,Blueprint.Thomson.Finite.RFCatalogue.rf1312]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even041.PairData
