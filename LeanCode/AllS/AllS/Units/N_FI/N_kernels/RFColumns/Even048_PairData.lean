import AllS.Units.N_FI.N_kernels.RFColumns.Even048_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even048.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/238:ℚ),(-1/14:ℚ),(8/17:ℚ),(-226/119:ℚ),(554/119:ℚ),(-83/119:ℚ),(-3011/119:ℚ),(5302/119:ℚ),(891/238:ℚ),(-10609/238:ℚ),(-797/119:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-1/476:ℚ),(5/119:ℚ),(-6/17:ℚ),(285/238:ℚ),(-121/238:ℚ),(-1311/238:ℚ),(916/119:ℚ),(2343/238:ℚ),(-4149/476:ℚ),(-857/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-2/119:ℚ),(29/119:ℚ),(-122/119:ℚ),(89/119:ℚ),(538/119:ℚ),(-1297/119:ℚ),(22/17:ℚ),(1787/119:ℚ),(-24/7:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-3/119:ℚ),(40/119:ℚ),(-155/119:ℚ),(216/119:ℚ),(-9/119:ℚ),(-64/7:ℚ),(17/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n3]
  all_goals ring
def num004 : List ℚ := [(-1/238:ℚ),(10/119:ℚ),(-151/238:ℚ),(292/119:ℚ),(-90/17:ℚ),(664/119:ℚ),(80/17:ℚ),(-4780/119:ℚ),(19381/238:ℚ),(-5914/119:ℚ),(-7825/238:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n4]
  all_goals ring
def num005 : List ℚ := [(1/476:ℚ),(-11/476:ℚ),(11/119:ℚ),(-25/119:ℚ),(33/238:ℚ),(95/34:ℚ),(-201/17:ℚ),(1089/119:ℚ),(2059/68:ℚ),(-3969/68:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n5]
  all_goals ring
def num006 : List ℚ := [(2/119:ℚ),(-32/119:ℚ),(169/119:ℚ),(-48/17:ℚ),(-11/119:ℚ),(1256/119:ℚ),(-2325/119:ℚ),(1160/119:ℚ),(37/7:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n6]
  all_goals ring
def num007 : List ℚ := [(-3/238:ℚ),(7/34:ℚ),(-8/7:ℚ),(305/119:ℚ),(-99/119:ℚ),(-838/119:ℚ),(196/17:ℚ),(-705/119:ℚ),(2977/238:ℚ),(-773/238:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n7]
  all_goals ring
def num008 : List ℚ := [(-1/476:ℚ),(1/34:ℚ),(-18/119:ℚ),(87/238:ℚ),(47/238:ℚ),(-811/238:ℚ),(268/119:ℚ),(2061/238:ℚ),(45/68:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n8]
  all_goals ring
def num009 : List ℚ := [(3/119:ℚ),(-45/119:ℚ),(207/119:ℚ),(-277/119:ℚ),(-49/17:ℚ),(1297/119:ℚ),(-1115/119:ℚ),(1/7:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n9]
  all_goals ring
def num010 : List ℚ := [(-1/119:ℚ),(2/17:ℚ),(-53/119:ℚ),(-26/119:ℚ),(71/17:ℚ),(-654/119:ℚ),(-999/119:ℚ),(2458/119:ℚ),(116/17:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n10]
  all_goals ring
def num011 : List ℚ := [(-1/238:ℚ),(9/238:ℚ),(-23/238:ℚ),(15/238:ℚ),(9/14:ℚ),(-1009/238:ℚ),(415/238:ℚ),(575/34:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even048.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even048.den,Blueprint.Thomson.Finite.RFCatalogue.rf1319]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even048.PairData
