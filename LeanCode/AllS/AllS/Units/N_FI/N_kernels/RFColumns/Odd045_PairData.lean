import AllS.Units.N_FI.N_kernels.RFColumns.Odd045_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(1/14:ℚ),(-11/7:ℚ),(2017/140:ℚ),(-2523/35:ℚ),(7429/35:ℚ),(-12539/35:ℚ),(19203/70:ℚ),(2591/35:ℚ),(-18623/70:ℚ),(2934/35:ℚ),(1439/20:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n0]
  all_goals ring
def num001 : List ℚ := [(-1/140:ℚ),(51/280:ℚ),(-277/140:ℚ),(3333/280:ℚ),(-304/7:ℚ),(2745/28:ℚ),(-914/7:ℚ),(11471/140:ℚ),(1689/140:ℚ),(-12413/280:ℚ),(1221/140:ℚ),(299/40:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n1]
  all_goals ring
def num002 : List ℚ := [(-1/140:ℚ),(23/140:ℚ),(-43/28:ℚ),(258/35:ℚ),(-251/14:ℚ),(817/70:ℚ),(3299/70:ℚ),(-4366/35:ℚ),(15471/140:ℚ),(-207/20:ℚ),(-133/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n2]
  all_goals ring
def num003 : List ℚ := [(-1/56:ℚ),(103/280:ℚ),(-897/280:ℚ),(4163/280:ℚ),(-4847/140:ℚ),(307/140:ℚ),(33129/140:ℚ),(-101313/140:ℚ),(290707/280:ℚ),(-185373/280:ℚ),(-8769/280:ℚ),(8697/40:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(1/35:ℚ),(-47/70:ℚ),(463/70:ℚ),(-2467/70:ℚ),(7753/70:ℚ),(-14563/70:ℚ),(15313/70:ℚ),(-6509/70:ℚ),(-2283/70:ℚ),(167/5:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n4]
  all_goals ring
def num005 : List ℚ := [(1/70:ℚ),(-9/35:ℚ),(129/70:ℚ),(-45/7:ℚ),(127/14:ℚ),(298/35:ℚ),(-3373/70:ℚ),(2039/35:ℚ),(-64/5:ℚ),(-21/1:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n5]
  all_goals ring
def num006 : List ℚ := [(1/140:ℚ),(-17/140:ℚ),(13/20:ℚ),(33/70:ℚ),(-717/35:ℚ),(3536/35:ℚ),(-1231/5:ℚ),(22551/70:ℚ),(-26477/140:ℚ),(-2879/140:ℚ),(1263/20:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n6]
  all_goals ring
def num007 : List ℚ := [(1/70:ℚ),(-47/140:ℚ),(33/10:ℚ),(-614/35:ℚ),(771/14:ℚ),(-7243/70:ℚ),(7649/70:ℚ),(-244/5:ℚ),(-436/35:ℚ),(299/20:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n7]
  all_goals ring
def num008 : List ℚ := [(3/140:ℚ),(-53/140:ℚ),(37/14:ℚ),(-309/35:ℚ),(389/35:ℚ),(147/10:ℚ),(-905/14:ℚ),(2439/35:ℚ),(-323/28:ℚ),(-95/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd045.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.den,Blueprint.Thomson.Finite.RFCatalogue.rf1929]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData
