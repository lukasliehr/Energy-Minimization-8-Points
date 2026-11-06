import AllS.Units.N_FI.N_kernels.RFColumns.Even045_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even045.PairData
def num000 : List ℚ := [(0/1:ℚ),(-3/238:ℚ),(3/34:ℚ),(118/119:ℚ),(-1474/119:ℚ),(6577/119:ℚ),(-16453/119:ℚ),(22700/119:ℚ),(-6362/119:ℚ),(-53943/238:ℚ),(49197/238:ℚ),(1510/17:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n0]
  all_goals ring
def num001 : List ℚ := [(0/1:ℚ),(-6/119:ℚ),(15/17:ℚ),(-691/119:ℚ),(2215/119:ℚ),(-3027/119:ℚ),(-2603/119:ℚ),(16599/119:ℚ),(-23875/119:ℚ),(5813/119:ℚ),(2098/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(5/476:ℚ),(9/119:ℚ),(-761/238:ℚ),(2628/119:ℚ),(-1073/17:ℚ),(10317/119:ℚ),(-451/14:ℚ),(-5706/119:ℚ),(73/4:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n2]
  all_goals ring
def num003 : List ℚ := [(0/1:ℚ),(3/119:ℚ),(-29/119:ℚ),(-5/119:ℚ),(499/119:ℚ),(-1023/119:ℚ),(241/119:ℚ),(439/17:ℚ),(-49/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n3]
  all_goals ring
def num004 : List ℚ := [(3/238:ℚ),(-26/119:ℚ),(311/238:ℚ),(-40/17:ℚ),(-161/17:ℚ),(7760/119:ℚ),(-20627/119:ℚ),(31184/119:ℚ),(-40309/238:ℚ),(-17198/119:ℚ),(10777/34:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-3/119:ℚ),(94/119:ℚ),(-856/119:ℚ),(3538/119:ℚ),(-1006/17:ℚ),(2370/119:ℚ),(21656/119:ℚ),(-414/1:ℚ),(5971/17:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n5]
  all_goals ring
def num006 : List ℚ := [(-3/68:ℚ),(80/119:ℚ),(-358/119:ℚ),(214/119:ℚ),(5095/238:ℚ),(-9276/119:ℚ),(2336/17:ℚ),(-13738/119:ℚ),(89/4:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n6]
  all_goals ring
def num007 : List ℚ := [(1/34:ℚ),(-111/238:ℚ),(304/119:ℚ),(-122/17:ℚ),(1943/119:ℚ),(-4325/119:ℚ),(76/1:ℚ),(-15318/119:ℚ),(25923/238:ℚ),(-2521/34:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n7]
  all_goals ring
def num008 : List ℚ := [(0/1:ℚ),(9/119:ℚ),(-145/119:ℚ),(741/119:ℚ),(-1405/119:ℚ),(27/119:ℚ),(5037/119:ℚ),(-1391/17:ℚ),(343/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n8]
  all_goals ring
def num009 : List ℚ := [(-1/17:ℚ),(31/34:ℚ),(-552/119:ℚ),(2507/238:ℚ),(-317/17:ℚ),(8719/238:ℚ),(-5686/119:ℚ),(59/2:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n9]
  all_goals ring
def num010 : List ℚ := [(2/119:ℚ),(-30/119:ℚ),(132/119:ℚ),(-226/119:ℚ),(540/119:ℚ),(-1602/119:ℚ),(116/119:ℚ),(1006/17:ℚ),(-2170/17:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(6/119:ℚ),(-20/17:ℚ),(810/119:ℚ),(-216/17:ℚ),(-230/119:ℚ),(5492/119:ℚ),(-1510/17:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even045.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even045.den,Blueprint.Thomson.Finite.RFCatalogue.rf1316]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even045.PairData
