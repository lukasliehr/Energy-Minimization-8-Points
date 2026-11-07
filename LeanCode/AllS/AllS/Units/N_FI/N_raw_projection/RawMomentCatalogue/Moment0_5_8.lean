import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_5_8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,1,1),(-5/3:ℚ)),((1,2,0),(5/3:ℚ)),((2,0,1),(5/3:ℚ)),((3,1,0),(-5/3:ℚ)),((5,0,0),(1/3:ℚ)),((0,1,2),(-8/3:ℚ)),((0,4,0),(2/3:ℚ)),((1,2,1),(8:ℚ)),((2,0,2),(4:ℚ)),((2,3,0),(-16/3:ℚ)),((3,1,1),(-32/3:ℚ)),((4,2,0),(20/3:ℚ)),((5,0,1),(8/3:ℚ)),((6,1,0),(-8/3:ℚ)),((8,0,0),(1/3:ℚ)),((0,2,3),(68/3:ℚ)),((0,5,1),(-4/3:ℚ)),((1,0,4),(-26/3:ℚ)),((1,3,2),(-220/3:ℚ)),((1,6,0),(4/3:ℚ)),((2,1,3),(-40/3:ℚ)),((2,4,1),(80:ℚ)),((3,2,2),(120:ℚ)),((3,5,0),(-88/3:ℚ)),((4,0,3),(50/3:ℚ)),((4,3,1),(-470/3:ℚ)),((5,1,2),(-86:ℚ)),((5,4,0),(182/3:ℚ)),((6,2,1),(364/3:ℚ)),((7,0,2),(52/3:ℚ)),((7,3,0),(-52:ℚ)),((8,1,1),(-39:ℚ)),((9,2,0),(65/3:ℚ)),((10,0,1),(13/3:ℚ)),((11,1,0),(-13/3:ℚ)),((13,0,0),(1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,1,1),(-35:ℤ)),((1,2,0),(35:ℤ)),((2,0,1),(35:ℤ)),((3,1,0),(-35:ℤ)),((5,0,0),(7:ℤ)),((0,1,2),(-56:ℤ)),((0,4,0),(14:ℤ)),((1,2,1),(168:ℤ)),((2,0,2),(84:ℤ)),((2,3,0),(-112:ℤ)),((3,1,1),(-224:ℤ)),((4,2,0),(140:ℤ)),((5,0,1),(56:ℤ)),((6,1,0),(-56:ℤ)),((8,0,0),(7:ℤ)),((0,2,3),(476:ℤ)),((0,5,1),(-28:ℤ)),((1,0,4),(-182:ℤ)),((1,3,2),(-1540:ℤ)),((1,6,0),(28:ℤ)),((2,1,3),(-280:ℤ)),((2,4,1),(1680:ℤ)),((3,2,2),(2520:ℤ)),((3,5,0),(-616:ℤ)),((4,0,3),(350:ℤ)),((4,3,1),(-3290:ℤ)),((5,1,2),(-1806:ℤ)),((5,4,0),(1274:ℤ)),((6,2,1),(2548:ℤ)),((7,0,2),(364:ℤ)),((7,3,0),(-1092:ℤ)),((8,1,1),(-819:ℤ)),((9,2,0),(455:ℤ)),((10,0,1),(91:ℤ)),((11,1,0),(-91:ℤ)),((13,0,0),(7:ℤ))]
def denominator16 : ℕ := 21
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,1,1),(-35:ℤ)),((1,2,0),(35:ℤ)),((2,0,1),(35:ℤ)),((3,1,0),(-35:ℤ)),((5,0,0),(7:ℤ)),((0,1,2),(-56:ℤ)),((0,4,0),(14:ℤ)),((1,2,1),(168:ℤ)),((2,0,2),(84:ℤ)),((2,3,0),(-112:ℤ)),((3,1,1),(-224:ℤ)),((4,2,0),(140:ℤ)),((5,0,1),(56:ℤ)),((6,1,0),(-56:ℤ)),((8,0,0),(7:ℤ)),((0,2,3),(476:ℤ)),((0,5,1),(-28:ℤ)),((1,0,4),(-182:ℤ)),((1,3,2),(-1540:ℤ)),((1,6,0),(28:ℤ)),((2,1,3),(-280:ℤ)),((2,4,1),(1680:ℤ)),((3,2,2),(2520:ℤ)),((3,5,0),(-616:ℤ)),((4,0,3),(350:ℤ)),((4,3,1),(-3290:ℤ)),((5,1,2),(-1806:ℤ)),((5,4,0),(1274:ℤ)),((6,2,1),(2548:ℤ)),((7,0,2),(364:ℤ)),((7,3,0),(-1092:ℤ)),((8,1,1),(-819:ℤ)),((9,2,0),(455:ℤ)),((10,0,1),(91:ℤ)),((11,1,0),(-91:ℤ)),((13,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 5 8 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_5_8
