import AllS.Units.N_FI.N_kernels.RFColumns.Even028_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even028.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/119:ℚ),(-10/119:ℚ),(3/119:ℚ),(146/119:ℚ),(-27/119:ℚ),(-1466/119:ℚ),(2113/119:ℚ),(2510/119:ℚ),(-5034/119:ℚ),(-1308/119:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(5/238:ℚ),(-67/238:ℚ),(269/238:ℚ),(-27/34:ℚ),(-145/34:ℚ),(1611/238:ℚ),(1595/238:ℚ),(-1259/238:ℚ),(-397/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(-3/119:ℚ),(6/17:ℚ),(-25/17:ℚ),(250/119:ℚ),(-33/119:ℚ),(-858/119:ℚ),(245/17:ℚ),(-10/7:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(-3/119:ℚ),(40/119:ℚ),(-155/119:ℚ),(216/119:ℚ),(-9/119:ℚ),(-64/7:ℚ),(17/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n3]
  all_goals ring
def num004 : List ℚ := [(-1/119:ℚ),(16/119:ℚ),(-89/119:ℚ),(174/119:ℚ),(185/119:ℚ),(-1086/119:ℚ),(37/119:ℚ),(3146/119:ℚ),(-156/17:ℚ),(-5386/119:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n4]
  all_goals ring
def num005 : List ℚ := [(-1/238:ℚ),(11/238:ℚ),(-30/119:ℚ),(143/238:ℚ),(195/119:ℚ),(-2631/238:ℚ),(1322/119:ℚ),(5869/238:ℚ),(-1787/34:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n5]
  all_goals ring
def num006 : List ℚ := [(3/119:ℚ),(-44/119:ℚ),(191/119:ℚ),(-216/119:ℚ),(-239/119:ℚ),(636/119:ℚ),(-149/17:ℚ),(72/7:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n6]
  all_goals ring
def num007 : List ℚ := [(-2/119:ℚ),(31/119:ℚ),(-160/119:ℚ),(367/119:ℚ),(-44/17:ℚ),(-149/17:ℚ),(3368/119:ℚ),(-2043/119:ℚ),(814/119:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(-1/119:ℚ),(13/119:ℚ),(2/17:ℚ),(-326/119:ℚ),(235/119:ℚ),(175/17:ℚ),(-56/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n8]
  all_goals ring
def num009 : List ℚ := [(4/119:ℚ),(-8/17:ℚ),(216/119:ℚ),(-16/17:ℚ),(-652/119:ℚ),(1160/119:ℚ),(-48/7:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n9]
  all_goals ring
def num010 : List ℚ := [(-1/119:ℚ),(16/119:ℚ),(-69/119:ℚ),(4/7:ℚ),(19/17:ℚ),(-592/119:ℚ),(897/119:ℚ),(228/17:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n10]
  all_goals ring
def num011 : List ℚ := [(1/238:ℚ),(-2/119:ℚ),(13/238:ℚ),(16/119:ℚ),(-661/238:ℚ),(274/119:ℚ),(449/34:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even028.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even028.den,Blueprint.Thomson.Finite.RFCatalogue.rf1059]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even028.PairData
