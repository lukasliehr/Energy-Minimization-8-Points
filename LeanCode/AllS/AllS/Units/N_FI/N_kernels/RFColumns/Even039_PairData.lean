import AllS.Units.N_FI.N_kernels.RFColumns.Even039_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even039.PairData
def num000 : List ℚ := [(0/1:ℚ),(1/10948:ℚ),(-19/10948:ℚ),(613/54740:ℚ),(-17/644:ℚ),(727/13685:ℚ),(-20359/27370:ℚ),(19563/3910:ℚ),(-458373/27370:ℚ),(1721229/54740:ℚ),(-1487499/54740:ℚ),(-780847/54740:ℚ),(25817/460:ℚ),(-914559/27370:ℚ),(-31030/2737:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n0]
  all_goals ring
def num001 : List ℚ := [(1/27370:ℚ),(-19/27370:ℚ),(66/13685:ℚ),(-467/27370:ℚ),(914/13685:ℚ),(-11703/27370:ℚ),(25562/13685:ℚ),(-54289/13685:ℚ),(1573/1610:ℚ),(387147/27370:ℚ),(-60424/1955:ℚ),(121369/5474:ℚ),(32323/2737:ℚ),(-789/34:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n1]
  all_goals ring
def num002 : List ℚ := [(0/1:ℚ),(1/54740:ℚ),(-1/7820:ℚ),(-337/54740:ℚ),(193/1564:ℚ),(-27619/27370:ℚ),(118493/27370:ℚ),(-53877/5474:ℚ),(53255/5474:ℚ),(204213/54740:ℚ),(-1106467/54740:ℚ),(1032691/54740:ℚ),(-2133/644:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n2]
  all_goals ring
def num003 : List ℚ := [(-1/27370:ℚ),(8/13685:ℚ),(-13/5474:ℚ),(-97/13685:ℚ),(206/1955:ℚ),(-1529/2737:ℚ),(24882/13685:ℚ),(-38867/13685:ℚ),(-29611/27370:ℚ),(23151/1955:ℚ),(-552763/27370:ℚ),(320/23:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n3]
  all_goals ring
def num004 : List ℚ := [(-1/54740:ℚ),(19/54740:ℚ),(-121/54740:ℚ),(27/54740:ℚ),(123/1955:ℚ),(-4309/13685:ℚ),(9871/27370:ℚ),(10053/3910:ℚ),(-794697/54740:ℚ),(2116731/54740:ℚ),(-3244853/54740:ℚ),(414979/10948:ℚ),(706227/27370:ℚ),(-254673/5474:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n4]
  all_goals ring
def num005 : List ℚ := [(0/1:ℚ),(-1/3910:ℚ),(3/782:ℚ),(-753/27370:ℚ),(689/3910:ℚ),(-14751/13685:ℚ),(62413/13685:ℚ),(-30273/2737:ℚ),(8383/805:ℚ),(512949/27370:ℚ),(-2054259/27370:ℚ),(406749/3910:ℚ),(-47607/782:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n5]
  all_goals ring
def num006 : List ℚ := [(1/54740:ℚ),(-11/54740:ℚ),(-3/1564:ℚ),(367/10948:ℚ),(-551/5474:ℚ),(-12783/27370:ℚ),(20275/5474:ℚ),(-267773/27370:ℚ),(20423/1564:ℚ),(-436967/54740:ℚ),(-8949/3220:ℚ),(4131/644:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n6]
  all_goals ring
def num007 : List ℚ := [(0/1:ℚ),(-13/54740:ℚ),(39/7820:ℚ),(-273/7820:ℚ),(815/10948:ℚ),(3279/27370:ℚ),(-6347/27370:ℚ),(-12289/3910:ℚ),(403147/27370:ℚ),(-1715873/54740:ℚ),(1917589/54740:ℚ),(-860011/54740:ℚ),(35043/10948:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n7]
  all_goals ring
def num008 : List ℚ := [(-1/27370:ℚ),(9/13685:ℚ),(-8/1955:ℚ),(103/5474:ℚ),(-2003/13685:ℚ),(1644/1955:ℚ),(-31506/13685:ℚ),(3943/1955:ℚ),(116159/27370:ℚ),(-205713/13685:ℚ),(35154/1955:ℚ),(-4319/782:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n8]
  all_goals ring
def num009 : List ℚ := [(0/1:ℚ),(2/13685:ℚ),(-67/13685:ℚ),(776/13685:ℚ),(-588/1955:ℚ),(12108/13685:ℚ),(-4254/1955:ℚ),(75976/13685:ℚ),(-132308/13685:ℚ),(116066/13685:ℚ),(-503/161:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n9]
  all_goals ring
def num010 : List ℚ := [(1/54740:ℚ),(-1/2380:ℚ),(47/10948:ℚ),(-933/54740:ℚ),(-43/1610:ℚ),(303/782:ℚ),(-20021/27370:ℚ),(-29541/27370:ℚ),(255813/54740:ℚ),(-193267/54740:ℚ),(-334353/54740:ℚ),(20821/1564:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n10]
  all_goals ring
def num011 : List ℚ := [(0/1:ℚ),(1/2737:ℚ),(-59/13685:ℚ),(376/13685:ℚ),(-2628/13685:ℚ),(13602/13685:ℚ),(-4742/1955:ℚ),(15104/13685:ℚ),(12564/1955:ℚ),(-210463/13685:ℚ),(5567/391:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.n11]
  all_goals ring
def denominator : List ℚ := [(-1/13685:ℚ),(11/13685:ℚ),(1/391:ℚ),(-817/13685:ℚ),(3053/13685:ℚ),(-1423/13685:ℚ),(-10447/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even039.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even039.den,Blueprint.Thomson.Finite.RFCatalogue.rf1310]
  all_goals ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even039.PairData
