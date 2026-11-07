import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_3_8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,1,3),(-11/3:ℚ)),((0,4,1),(11/3:ℚ)),((1,2,2),(22:ℚ)),((1,5,0),(-11/3:ℚ)),((2,0,3),(22/3:ℚ)),((2,3,1),(-110/3:ℚ)),((3,1,2),(-110/3:ℚ)),((3,4,0),(55/3:ℚ)),((4,2,1),(55:ℚ)),((5,0,2),(11:ℚ)),((5,3,0),(-77/3:ℚ)),((6,1,1),(-77/3:ℚ)),((7,2,0),(44/3:ℚ)),((8,0,1),(11/3:ℚ)),((9,1,0),(-11/3:ℚ)),((11,0,0),(1/3:ℚ)),((0,0,4),(-3:ℚ)),((0,3,2),(-5:ℚ)),((1,1,3),(13:ℚ)),((1,4,1),(5:ℚ)),((2,2,2),(-5:ℚ)),((3,0,3),(-11:ℚ)),((3,3,1),(-5:ℚ)),((4,1,2),(10:ℚ)),((5,2,1),(1:ℚ)),((6,0,2),(-2:ℚ)),((0,2,3),(34/3:ℚ)),((0,5,1),(28/3:ℚ)),((1,0,4),(-10/3:ℚ)),((1,3,2),(10/3:ℚ)),((1,6,0),(-28/3:ℚ)),((2,1,3),(100/3:ℚ)),((2,4,1),(-50:ℚ)),((3,2,2),(-100:ℚ)),((3,5,0),(106/3:ℚ)),((4,0,3),(-95/3:ℚ)),((4,3,1),(395/3:ℚ)),((5,1,2),(97:ℚ)),((5,4,0),(-185/3:ℚ)),((6,2,1),(-352/3:ℚ)),((7,0,2),(-58/3:ℚ)),((7,3,0),(52:ℚ)),((8,1,1),(39:ℚ)),((9,2,0),(-65/3:ℚ)),((10,0,1),(-13/3:ℚ)),((11,1,0),(13/3:ℚ)),((13,0,0),(-1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,1,3),(-11:ℤ)),((0,4,1),(11:ℤ)),((1,2,2),(66:ℤ)),((1,5,0),(-11:ℤ)),((2,0,3),(22:ℤ)),((2,3,1),(-110:ℤ)),((3,1,2),(-110:ℤ)),((3,4,0),(55:ℤ)),((4,2,1),(165:ℤ)),((5,0,2),(33:ℤ)),((5,3,0),(-77:ℤ)),((6,1,1),(-77:ℤ)),((7,2,0),(44:ℤ)),((8,0,1),(11:ℤ)),((9,1,0),(-11:ℤ)),((11,0,0),(1:ℤ)),((0,0,4),(-9:ℤ)),((0,3,2),(-15:ℤ)),((1,1,3),(39:ℤ)),((1,4,1),(15:ℤ)),((2,2,2),(-15:ℤ)),((3,0,3),(-33:ℤ)),((3,3,1),(-15:ℤ)),((4,1,2),(30:ℤ)),((5,2,1),(3:ℤ)),((6,0,2),(-6:ℤ)),((0,2,3),(34:ℤ)),((0,5,1),(28:ℤ)),((1,0,4),(-10:ℤ)),((1,3,2),(10:ℤ)),((1,6,0),(-28:ℤ)),((2,1,3),(100:ℤ)),((2,4,1),(-150:ℤ)),((3,2,2),(-300:ℤ)),((3,5,0),(106:ℤ)),((4,0,3),(-95:ℤ)),((4,3,1),(395:ℤ)),((5,1,2),(291:ℤ)),((5,4,0),(-185:ℤ)),((6,2,1),(-352:ℤ)),((7,0,2),(-58:ℤ)),((7,3,0),(156:ℤ)),((8,1,1),(117:ℤ)),((9,2,0),(-65:ℤ)),((10,0,1),(-13:ℤ)),((11,1,0),(13:ℤ)),((13,0,0),(-1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 1 3 8 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_3_8
