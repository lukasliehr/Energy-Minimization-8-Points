import AllS.Units.N_FI.N_kernels.RFColumns.Odd016_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd016.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/70:ℚ),(-19/70:ℚ),(17/7:ℚ),(-88/7:ℚ),(1332/35:ℚ),(-2139/35:ℚ),(1039/35:ℚ),(1572/35:ℚ),(-423/10:ℚ),(-291/14:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n0]
  ring
def num001 : List ℚ := [(1/70:ℚ),(-1/4:ℚ),(13/7:ℚ),(-15/2:ℚ),(87/5:ℚ),(-151/7:ℚ),(289/35:ℚ),(117/14:ℚ),(-327/70:ℚ),(-53/28:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n1]
  ring
def num002 : List ℚ := [(1/70:ℚ),(-8/35:ℚ),(48/35:ℚ),(-124/35:ℚ),(59/35:ℚ),(56/5:ℚ),(-24/1:ℚ),(396/35:ℚ),(19/2:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n2]
  ring
def num003 : List ℚ := [(3/140:ℚ),(-51/140:ℚ),(83/35:ℚ),(-237/35:ℚ),(27/14:ℚ),(447/10:ℚ),(-4759/35:ℚ),(5829/35:ℚ),(-6529/140:ℚ),(-1747/28:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n3]
  ring
def num004 : List ℚ := [(0/1:ℚ),(-2/35:ℚ),(31/35:ℚ),(-202/35:ℚ),(699/35:ℚ),(-262/7:ℚ),(1109/35:ℚ),(2/7:ℚ),(-67/7:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n4]
  ring
def num005 : List ℚ := [(-1/70:ℚ),(3/14:ℚ),(-79/70:ℚ),(29/14:ℚ),(121/70:ℚ),(-743/70:ℚ),(599/70:ℚ),(13/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n5]
  ring
def num006 : List ℚ := [(-1/70:ℚ),(1/7:ℚ),(-6/35:ℚ),(-113/35:ℚ),(129/7:ℚ),(-1573/35:ℚ),(1802/35:ℚ),(-383/35:ℚ),(-253/14:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n6]
  ring
def num007 : List ℚ := [(-1/35:ℚ),(31/70:ℚ),(-20/7:ℚ),(681/70:ℚ),(-91/5:ℚ),(1153/70:ℚ),(-62/35:ℚ),(-53/14:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n7]
  ring
def num008 : List ℚ := [(-1/35:ℚ),(13/35:ℚ),(-57/35:ℚ),(15/7:ℚ),(25/7:ℚ),(-89/7:ℚ),(43/5:ℚ),(7/1:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.n8]
  ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd016.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd016.den,Blueprint.Thomson.Finite.RFCatalogue.rf1223]
  ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd016.PairData
