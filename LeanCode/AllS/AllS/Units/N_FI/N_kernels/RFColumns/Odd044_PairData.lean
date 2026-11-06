import AllS.Units.N_FI.N_kernels.RFColumns.Odd044_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd044.PairData
def num000 : List ℚ := [(0/1:ℚ),(19/7:ℚ),(-407/28:ℚ),(2/7:ℚ),(5155/28:ℚ),(-8193/14:ℚ),(22767/28:ℚ),(-3265/7:ℚ),(-2523/28:ℚ),(239/2:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n0]
  all_goals ring
def num001 : List ℚ := [(31/28:ℚ),(-55/14:ℚ),(-333/28:ℚ),(678/7:ℚ),(-7109/28:ℚ),(4821/14:ℚ),(-6059/28:ℚ),(-45/7:ℚ),(137/2:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n1]
  all_goals ring
def num002 : List ℚ := [(5/4:ℚ),(-7/1:ℚ),(23/4:ℚ),(37/2:ℚ),(-141/4:ℚ),(16/1:ℚ),(17/4:ℚ),(-7/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n2]
  all_goals ring
def num003 : List ℚ := [(-1/2:ℚ),(41/14:ℚ),(-445/28:ℚ),(249/7:ℚ),(2389/28:ℚ),(-8479/14:ℚ),(35381/28:ℚ),(-9014/7:ℚ),(1943/4:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(-9/2:ℚ),(51/7:ℚ),(787/14:ℚ),(-1870/7:ℚ),(7575/14:ℚ),(-3989/7:ℚ),(547/2:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n4]
  all_goals ring
def num005 : List ℚ := [(7/4:ℚ),(-21/2:ℚ),(49/4:ℚ),(21/1:ℚ),(-231/4:ℚ),(91/2:ℚ),(-49/4:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n5]
  all_goals ring
def num006 : List ℚ := [(-5/4:ℚ),(1/14:ℚ),(53/4:ℚ),(225/7:ℚ),(-1035/4:ℚ),(8137/14:ℚ),(-16803/28:ℚ),(270/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n6]
  all_goals ring
def num007 : List ℚ := [(-9/4:ℚ),(51/14:ℚ),(787/28:ℚ),(-935/7:ℚ),(7575/28:ℚ),(-3989/14:ℚ),(547/4:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n7]
  all_goals ring
def num008 : List ℚ := [(-3/4:ℚ),(23/14:ℚ),(157/28:ℚ),(-31/7:ℚ),(-75/28:ℚ),(279/14:ℚ),(69/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.n8]
  all_goals ring
def denominator : List ℚ := [(-1/7:ℚ),(2/7:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd044.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd044.den,Blueprint.Thomson.Finite.RFCatalogue.rf1928]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd044.PairData
