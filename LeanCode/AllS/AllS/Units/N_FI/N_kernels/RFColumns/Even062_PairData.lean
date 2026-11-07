import AllS.Units.N_FI.N_kernels.RFColumns.Even062_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even062.PairData
def num000 : List ℚ := [(0/1:ℚ),(-39/136:ℚ),(2689/476:ℚ),(-44179/952:ℚ),(109339/476:ℚ),(-3235/4:ℚ),(474441/238:ℚ),(-1441827/476:ℚ),(62153/34:ℚ),(1867595/952:ℚ),(-2003683/476:ℚ),(1822249/952:ℚ),(76497/68:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n0]
  all_goals ring
def num001 : List ℚ := [(-2/17:ℚ),(265/119:ℚ),(-2083/119:ℚ),(9578/119:ℚ),(-28096/119:ℚ),(44790/119:ℚ),(366/7:ℚ),(-28088/17:ℚ),(391222/119:ℚ),(-283495/119:ℚ),(-51347/119:ℚ),(26186/17:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n1]
  all_goals ring
def num002 : List ℚ := [(-8/119:ℚ),(200/119:ℚ),(-2076/119:ℚ),(11868/119:ℚ),(-42276/119:ℚ),(100764/119:ℚ),(-146428/119:ℚ),(13836/17:ℚ),(27836/119:ℚ),(-89108/119:ℚ),(184/1:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n2]
  all_goals ring
def num003 : List ℚ := [(1/17:ℚ),(-67/119:ℚ),(-52/119:ℚ),(1844/119:ℚ),(-7198/119:ℚ),(15366/119:ℚ),(-4996/119:ℚ),(-48604/119:ℚ),(13561/17:ℚ),(-637/1:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n3]
  all_goals ring
def num004 : List ℚ := [(7/136:ℚ),(-151/136:ℚ),(10373/952:ℚ),(-60653/952:ℚ),(125313/476:ℚ),(-401169/476:ℚ),(1002377/476:ℚ),(-1717937/476:ℚ),(184445/56:ℚ),(449539/952:ℚ),(-4164887/952:ℚ),(546617/136:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n4]
  all_goals ring
def num005 : List ℚ := [(-1/17:ℚ),(240/119:ℚ),(-2547/119:ℚ),(832/7:ℚ),(-49086/119:ℚ),(102880/119:ℚ),(-73902/119:ℚ),(-226624/119:ℚ),(747781/119:ℚ),(-133040/17:ℚ),(73815/17:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n5]
  all_goals ring
def num006 : List ℚ := [(-2/17:ℚ),(290/119:ℚ),(-2224/119:ℚ),(9328/119:ℚ),(-33052/119:ℚ),(5732/7:ℚ),(-190208/119:ℚ),(223840/119:ℚ),(-7878/7:ℚ),(102/1:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n6]
  all_goals ring
def num007 : List ℚ := [(9/136:ℚ),(-108/119:ℚ),(235/136:ℚ),(2850/119:ℚ),(-83525/476:ℚ),(82410/119:ℚ),(-842995/476:ℚ),(343622/119:ℚ),(-3095557/952:ℚ),(261146/119:ℚ),(-128593/136:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n7]
  all_goals ring
def num008 : List ℚ := [(3/17:ℚ),(-379/119:ℚ),(364/17:ℚ),(-9388/119:ℚ),(20598/119:ℚ),(-12042/119:ℚ),(-3484/7:ℚ),(8452/7:ℚ),(-20229/17:ℚ),(4459/17:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(-36/119:ℚ),(1180/119:ℚ),(-11604/119:ℚ),(47276/119:ℚ),(-107180/119:ℚ),(150292/119:ℚ),(-121052/119:ℚ),(380/1:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n9]
  all_goals ring
def num010 : List ℚ := [(1/68:ℚ),(-75/476:ℚ),(-47/17:ℚ),(3897/119:ℚ),(-30455/238:ℚ),(59555/238:ℚ),(-13925/119:ℚ),(-98163/119:ℚ),(117673/68:ℚ),(-108437/68:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n10]
  all_goals ring
def num011 : List ℚ := [(2/17:ℚ),(-368/119:ℚ),(392/17:ℚ),(-10032/119:ℚ),(21348/119:ℚ),(-10448/119:ℚ),(-70696/119:ℚ),(148080/119:ℚ),(-18542/17:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.n11]
  all_goals ring
def denominator : List ℚ := [(-1/119:ℚ),(12/119:ℚ),(-30/119:ℚ),(-36/119:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even062.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even062.den,Blueprint.Thomson.Finite.RFCatalogue.rf1654]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even062.PairData
