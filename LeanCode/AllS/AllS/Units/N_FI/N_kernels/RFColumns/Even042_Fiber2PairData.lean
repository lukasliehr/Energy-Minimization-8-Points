import AllS.Units.N_FI.N_kernels.RFColumns.Even042_Evaluations
import AllS.Units.N_FI.N_kernels.RFParityListSupport
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even042.Fiber2PairData
def num000 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(-9/218960:ℚ),(2/1955:ℚ),(-1891/218960:ℚ),(151/109480:ℚ),(1045/1904:ℚ),(-69773/13685:ℚ),(5546141/218960:ℚ),(-8861061/109480:ℚ),(38523053/218960:ℚ),(-731575/2737:ℚ),(64403839/218960:ℚ),(-3921493/15640:ℚ),(7399113/43792:ℚ),(-866786/13685:ℚ),(-4415161/218960:ℚ),(410583/15640:ℚ)]
theorem num000_eval (a : ℝ) : evalRationalList num000 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n0 a := by
  norm_num [num000,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n0]
  ring
def num001 : List ℚ := [(0/1:ℚ),(-1/437920:ℚ),(3/109480:ℚ),(29/437920:ℚ),(-29/9520:ℚ),(10463/437920:ℚ),(-2557/27370:ℚ),(79069/437920:ℚ),(219/218960:ℚ),(-380907/437920:ℚ),(41043/21896:ℚ),(-380609/437920:ℚ),(-569717/218960:ℚ),(1670861/437920:ℚ),(9777/54740:ℚ),(-2307/736:ℚ),(2037/1360:ℚ)]
theorem num001_eval (a : ℝ) : evalRationalList num001 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n1 a := by
  norm_num [num001,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n1]
  ring
def num002 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(3/109480:ℚ),(-83/109480:ℚ),(79/10948:ℚ),(-24/2737:ℚ),(-44479/109480:ℚ),(463441/109480:ℚ),(-616937/27370:ℚ),(1037478/13685:ℚ),(-2635589/15640:ℚ),(26669607/109480:ℚ),(-2291925/10948:ℚ),(202938/2737:ℚ),(579763/21896:ℚ),(-4647/184:ℚ)]
theorem num002_eval (a : ℝ) : evalRationalList num002 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n2 a := by
  norm_num [num002,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n2]
  ring
def num003 : List ℚ := [(0/1:ℚ),(0/1:ℚ),(0/1:ℚ),(-1/54740:ℚ),(6/13685:ℚ),(-249/54740:ℚ),(21/782:ℚ),(-521/5474:ℚ),(2748/13685:ℚ),(-6217/27370:ℚ),(-265/2737:ℚ),(66971/54740:ℚ),(-37206/13685:ℚ),(175/68:ℚ),(-203/230:ℚ)]
theorem num003_eval (a : ℝ) : evalRationalList num003 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n3 a := by
  norm_num [num003,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n3]
  ring
def num004 : List ℚ := [(0/1:ℚ),(11/218960:ℚ),(-129/109480:ℚ),(117/12880:ℚ),(61/10948:ℚ),(-133729/218960:ℚ),(24919/4760:ℚ),(-5402839/218960:ℚ),(292643/3910:ℚ),(-32698303/218960:ℚ),(3977581/21896:ℚ),(-525227/6256:ℚ),(-1186699/10948:ℚ),(8870929/43792:ℚ),(-1601671/15640:ℚ),(-1121321/43792:ℚ),(66969/1955:ℚ)]
theorem num004_eval (a : ℝ) : evalRationalList num004 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n4 a := by
  norm_num [num004,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n4]
  ring
def num005 : List ℚ := [(1/437920:ℚ),(-3/109480:ℚ),(-1/437920:ℚ),(53/31280:ℚ),(-5511/437920:ℚ),(129/2737:ℚ),(-44777/437920:ℚ),(12757/218960:ℚ),(252667/437920:ℚ),(-289047/109480:ℚ),(2283973/437920:ℚ),(-507027/218960:ℚ),(-222867/19040:ℚ),(206631/7820:ℚ),(-16665/736:ℚ),(221949/31280:ℚ)]
theorem num005_eval (a : ℝ) : evalRationalList num005 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n5 a := by
  norm_num [num005,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n5]
  ring
def num006 : List ℚ := [(0/1:ℚ),(-1/27370:ℚ),(12/13685:ℚ),(-377/54740:ℚ),(-83/27370:ℚ),(24721/54740:ℚ),(-53523/13685:ℚ),(505663/27370:ℚ),(-109059/1955:ℚ),(1515854/13685:ℚ),(-112836/805:ℚ),(5475899/54740:ℚ),(-588747/27370:ℚ),(-201883/10948:ℚ),(1161/115:ℚ)]
theorem num006_eval (a : ℝ) : evalRationalList num006 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n6 a := by
  norm_num [num006,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n6]
  ring
def num007 : List ℚ := [(0/1:ℚ),(-1/54740:ℚ),(7/15640:ℚ),(-41/10948:ℚ),(1/782:ℚ),(3088/13685:ℚ),(-236127/109480:ℚ),(2603/230:ℚ),(-109630/2737:ℚ),(800249/7820:ℚ),(-20977997/109480:ℚ),(13929551/54740:ℚ),(-5885359/27370:ℚ),(2158097/27370:ℚ),(3240283/109480:ℚ),(-61629/1955:ℚ)]
theorem num007_eval (a : ℝ) : evalRationalList num007 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n7 a := by
  norm_num [num007,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n7]
  ring
def num008 : List ℚ := [(0/1:ℚ),(-1/218960:ℚ),(1/21896:ℚ),(1/54740:ℚ),(-79/54740:ℚ),(739/218960:ℚ),(1181/109480:ℚ),(-471/13685:ℚ),(-545/5474:ℚ),(13171/31280:ℚ),(-5393/109480:ℚ),(-67621/54740:ℚ),(12477/10948:ℚ),(69/272:ℚ),(-6391/15640:ℚ)]
theorem num008_eval (a : ℝ) : evalRationalList num008 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n8 a := by
  norm_num [num008,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n8]
  ring
def num009 : List ℚ := [(0/1:ℚ),(1/27370:ℚ),(-53/54740:ℚ),(27/3220:ℚ),(39/54740:ℚ),(-30159/54740:ℚ),(130381/27370:ℚ),(-583659/27370:ℚ),(1596461/27370:ℚ),(-272684/2737:ℚ),(5442219/54740:ℚ),(-461857/10948:ℚ),(-712849/54740:ℚ),(1471/92:ℚ)]
theorem num009_eval (a : ℝ) : evalRationalList num009 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n9 a := by
  norm_num [num009,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n9]
  ring
def num010 : List ℚ := [(0/1:ℚ),(-1/15640:ℚ),(1/782:ℚ),(-53/7820:ℚ),(-541/13685:ℚ),(77771/109480:ℚ),(-113423/27370:ℚ),(68147/5474:ℚ),(-9806/595:ℚ),(-1358353/109480:ℚ),(2273213/27370:ℚ),(-6957611/54740:ℚ),(200611/2737:ℚ),(1364877/109480:ℚ),(-99271/3910:ℚ)]
theorem num010_eval (a : ℝ) : evalRationalList num010 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n10 a := by
  norm_num [num010,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n10]
  ring
def num011 : List ℚ := [(-1/218960:ℚ),(1/21896:ℚ),(3/27370:ℚ),(-181/54740:ℚ),(779/43792:ℚ),(-37/920:ℚ),(9/782:ℚ),(277/1610:ℚ),(-120179/218960:ℚ),(91087/109480:ℚ),(849/13685:ℚ),(-26793/10948:ℚ),(100251/31280:ℚ),(-19719/15640:ℚ)]
theorem num011_eval (a : ℝ) : evalRationalList num011 a = -evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.n11 a := by
  norm_num [num011,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.n11]
  ring
def denominator : List ℚ := [(0/1:ℚ),(-1/13685:ℚ),(13/13685:ℚ),(12/13685:ℚ),(-876/13685:ℚ),(4722/13685:ℚ),(-8346/13685:ℚ),(-4548/13685:ℚ),(33156/13685:ℚ),(-37817/13685:ℚ),(1/1:ℚ)]
theorem denominator_eval (a : ℝ) : evalRationalList denominator a=evalQPoly Blueprint.Thomson.Finite.RFColumnProofs.Even042.den a := by
  norm_num [denominator,evalRationalList,evalQPoly,Blueprint.Thomson.Finite.RFColumnProofs.Even042.den,Blueprint.Thomson.Finite.RFCatalogue.rf1313]
  ring_nf <;> simp
def terms : List (Tag × List ℚ) := [((0,0,0),num000),((0,1,0),num001),((0,2,0),num002),((0,3,0),num003),((1,0,0),num004),((1,1,0),num005),((1,2,0),num006),((2,0,0),num007),((2,1,0),num008),((2,2,0),num009),((3,0,0),num010),((3,1,0),num011)]
#print axioms denominator_eval
end Blueprint.Thomson.Finite.RFColumnProofs.Even042.Fiber2PairData
