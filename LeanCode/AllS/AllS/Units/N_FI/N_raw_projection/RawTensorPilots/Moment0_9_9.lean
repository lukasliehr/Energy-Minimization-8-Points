import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawTensorPilots.Moment0_9_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,0,3),(2:ℚ)),((0,3,1),(-6:ℚ)),((1,1,2),(-18:ℚ)),((1,4,0),(6:ℚ)),((2,2,1),(36:ℚ)),((3,0,2),(12:ℚ)),((3,3,0),(-20:ℚ)),((4,1,1),(-30:ℚ)),((5,2,0),(18:ℚ)),((6,0,1),(6:ℚ)),((7,1,0),(-6:ℚ)),((9,0,0),(2/3:ℚ)),((0,0,6),(7:ℚ)),((0,3,4),(6:ℚ)),((0,6,2),(39:ℚ)),((0,9,0),(4/3:ℚ)),((1,1,5),(-90:ℚ)),((1,4,3),(120:ℚ)),((1,7,1),(-66:ℚ)),((2,2,4),(423:ℚ)),((2,5,2),(-450:ℚ)),((2,8,0),(27:ℚ)),((3,0,5),(24:ℚ)),((3,3,3),(-1180:ℚ)),((3,6,1),(504:ℚ)),((4,1,4),(-402:ℚ)),((4,4,2),(1890:ℚ)),((4,7,0),(-180:ℚ)),((5,2,3),(1512:ℚ)),((5,5,1),(-1512:ℚ)),((6,0,4),(126:ℚ)),((6,3,2),(-2520:ℚ)),((6,6,0),(462:ℚ)),((7,1,3),(-720:ℚ)),((7,4,1),(1980:ℚ)),((8,2,2),(1485:ℚ)),((8,5,0),(-594:ℚ)),((9,0,3),(110:ℚ)),((9,3,1),(-1320:ℚ)),((10,1,2),(-396:ℚ)),((10,4,0),(429:ℚ)),((11,2,1),(468:ℚ)),((12,0,2),(39:ℚ)),((12,3,0),(-182:ℚ)),((13,1,1),(-84:ℚ)),((14,2,0),(45:ℚ)),((15,0,1),(6:ℚ)),((16,1,0),(-6:ℚ)),((18,0,0),(1/3:ℚ))]
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 9 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawTensorPilots.Moment0_9_9
