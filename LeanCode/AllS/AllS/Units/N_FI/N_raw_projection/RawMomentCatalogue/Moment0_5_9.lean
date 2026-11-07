import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_5_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,1,1),(-5/3:ℚ)),((1,2,0),(5/3:ℚ)),((2,0,1),(5/3:ℚ)),((3,1,0),(-5/3:ℚ)),((5,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,1,4),(-17/3:ℚ)),((0,4,2),(65/3:ℚ)),((0,7,0),(4/3:ℚ)),((1,2,3),(170/3:ℚ)),((1,5,1),(-34:ℚ)),((2,0,4),(-25/3:ℚ)),((2,3,2),(-170:ℚ)),((2,6,0),(37/3:ℚ)),((3,1,3),(-160/3:ℚ)),((3,4,1),(550/3:ℚ)),((4,2,2),(230:ℚ)),((4,5,0),(-193/3:ℚ)),((5,0,3),(83/3:ℚ)),((5,3,1),(-799/3:ℚ)),((6,1,2),(-377/3:ℚ)),((6,4,0),(98:ℚ)),((7,2,1),(168:ℚ)),((8,0,2),(21:ℚ)),((8,3,0),(-70:ℚ)),((9,1,1),(-140/3:ℚ)),((10,2,0),(77/3:ℚ)),((11,0,1),(14/3:ℚ)),((12,1,0),(-14/3:ℚ)),((14,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,1,1),(-35:ℤ)),((1,2,0),(35:ℤ)),((2,0,1),(35:ℤ)),((3,1,0),(-35:ℤ)),((5,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,1,4),(-119:ℤ)),((0,4,2),(455:ℤ)),((0,7,0),(28:ℤ)),((1,2,3),(1190:ℤ)),((1,5,1),(-714:ℤ)),((2,0,4),(-175:ℤ)),((2,3,2),(-3570:ℤ)),((2,6,0),(259:ℤ)),((3,1,3),(-1120:ℤ)),((3,4,1),(3850:ℤ)),((4,2,2),(4830:ℤ)),((4,5,0),(-1351:ℤ)),((5,0,3),(581:ℤ)),((5,3,1),(-5593:ℤ)),((6,1,2),(-2639:ℤ)),((6,4,0),(2058:ℤ)),((7,2,1),(3528:ℤ)),((8,0,2),(441:ℤ)),((8,3,0),(-1470:ℤ)),((9,1,1),(-980:ℤ)),((10,2,0),(539:ℤ)),((11,0,1),(98:ℤ)),((12,1,0),(-98:ℤ)),((14,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 5 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_5_9
