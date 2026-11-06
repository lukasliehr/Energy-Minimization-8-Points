import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_3_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,0,1),(1:ℚ)),((1,1,0),(-1:ℚ)),((3,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,0,4),(7:ℚ)),((0,3,2),(-11:ℚ)),((0,6,0),(-4/3:ℚ)),((1,1,3),(-58:ℚ)),((1,4,1),(14:ℚ)),((2,2,2),(123:ℚ)),((2,5,0),(-3:ℚ)),((3,0,3),(91/3:ℚ)),((3,3,1),(-101:ℚ)),((4,1,2),(-96:ℚ)),((4,4,0),(29:ℚ)),((5,2,1),(102:ℚ)),((6,0,2),(17:ℚ)),((6,3,0),(-109/3:ℚ)),((7,1,1),(-35:ℚ)),((8,2,0),(18:ℚ)),((9,0,1),(4:ℚ)),((10,1,0),(-4:ℚ)),((12,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,1),(21:ℤ)),((1,1,0),(-21:ℤ)),((3,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,0,4),(147:ℤ)),((0,3,2),(-231:ℤ)),((0,6,0),(-28:ℤ)),((1,1,3),(-1218:ℤ)),((1,4,1),(294:ℤ)),((2,2,2),(2583:ℤ)),((2,5,0),(-63:ℤ)),((3,0,3),(637:ℤ)),((3,3,1),(-2121:ℤ)),((4,1,2),(-2016:ℤ)),((4,4,0),(609:ℤ)),((5,2,1),(2142:ℤ)),((6,0,2),(357:ℤ)),((6,3,0),(-763:ℤ)),((7,1,1),(-735:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 3 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_3_9
