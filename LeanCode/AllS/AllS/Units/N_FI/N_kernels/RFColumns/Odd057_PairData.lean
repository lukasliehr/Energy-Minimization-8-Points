import AllS.Units.N_FI.N_kernels.RFColumns.Odd057_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd057.PairData
def num000 : List ℚ := [(0/1:ℚ),(-3/280:ℚ),(5/28:ℚ),(-309/280:ℚ),(99/35:ℚ),(-173/140:ℚ),(-57/10:ℚ),(701/140:ℚ),(-167/35:ℚ),(7101/280:ℚ),(-2859/140:ℚ),(1051/280:ℚ),(248/35:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n0]
  all_goals ring
def num001 : List ℚ := [(-1/280:ℚ),(13/280:ℚ),(-11/56:ℚ),(71/280:ℚ),(-13/140:ℚ),(211/140:ℚ),(-447/140:ℚ),(-459/140:ℚ),(3371/280:ℚ),(-487/56:ℚ),(-31/56:ℚ),(607/280:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n1]
  all_goals ring
def num002 : List ℚ := [(-1/280:ℚ),(1/28:ℚ),(-3/56:ℚ),(-13/35:ℚ),(101/140:ℚ),(137/70:ℚ),(-437/140:ℚ),(-131/35:ℚ),(1207/280:ℚ),(-247/140:ℚ),(-13/8:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n2]
  all_goals ring
def num003 : List ℚ := [(1/280:ℚ),(-3/40:ℚ),(183/280:ℚ),(-809/280:ℚ),(831/140:ℚ),(-13/20:ℚ),(-523/28:ℚ),(661/28:ℚ),(-607/280:ℚ),(7499/280:ℚ),(-11817/280:ℚ),(7831/280:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n3]
  all_goals ring
def num004 : List ℚ := [(0/1:ℚ),(3/140:ℚ),(-1/4:ℚ),(33/35:ℚ),(-9/7:ℚ),(19/14:ℚ),(-187/70:ℚ),(-209/35:ℚ),(141/7:ℚ),(-2689/140:ℚ),(969/140:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n4]
  all_goals ring
def num005 : List ℚ := [(1/140:ℚ),(-1/14:ℚ),(6/35:ℚ),(4/35:ℚ),(-5/14:ℚ),(27/35:ℚ),(-162/35:ℚ),(-68/35:ℚ),(1089/140:ℚ),(-11/2:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n5]
  all_goals ring
def num006 : List ℚ := [(1/280:ℚ),(-3/70:ℚ),(53/280:ℚ),(-4/7:ℚ),(243/140:ℚ),(-27/35:ℚ),(-349/28:ℚ),(744/35:ℚ),(537/280:ℚ),(-275/14:ℚ),(3373/280:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n6]
  all_goals ring
def num007 : List ℚ := [(1/140:ℚ),(-11/140:ℚ),(13/70:ℚ),(37/70:ℚ),(-2/1:ℚ),(-11/35:ℚ),(319/70:ℚ),(-97/14:ℚ),(799/140:ℚ),(-233/140:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n7]
  all_goals ring
def num008 : List ℚ := [(-1/70:ℚ),(31/140:ℚ),(-89/70:ℚ),(41/14:ℚ),(-9/70:ℚ),(-66/7:ℚ),(849/70:ℚ),(-757/70:ℚ),(209/35:ℚ),(-13/4:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.n8]
  all_goals ring
def denominator : List ℚ := [(1/35:ℚ),(-9/35:ℚ),(18/35:ℚ),(22/35:ℚ),(-67/35:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Odd057.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Odd057.den,Blueprint.Thomson.Finite.RFCatalogue.rf1941]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((1,0,0),num003),((1,1,0),num004),((1,2,0),num005),((2,0,0),num006),((2,1,0),num007),((3,0,0),num008)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Odd057.PairData
