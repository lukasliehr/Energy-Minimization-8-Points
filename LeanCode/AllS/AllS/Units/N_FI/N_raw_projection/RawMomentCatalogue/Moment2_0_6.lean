import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_6
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,2),(-5:ℚ)),((0,3,0),(10/3:ℚ)),((1,1,1),(20:ℚ)),((2,2,0),(-15:ℚ)),((3,0,1),(-10:ℚ)),((4,1,0),(10:ℚ)),((6,0,0),(-5/3:ℚ)),((0,1,2),(-14/3:ℚ)),((0,4,0),(26/3:ℚ)),((1,2,1),(32:ℚ)),((2,0,2),(-11:ℚ)),((2,3,0),(-100/3:ℚ)),((3,1,1),(-56/3:ℚ)),((4,2,0),(89/3:ℚ)),((5,0,1),(14/3:ℚ)),((6,1,0),(-32/3:ℚ)),((8,0,0),(4/3:ℚ)),((0,0,3),(-24:ℚ)),((0,3,1),(16:ℚ)),((1,1,2),(96:ℚ)),((2,2,1),(-72:ℚ)),((3,0,2),(-48:ℚ)),((4,1,1),(48:ℚ)),((6,0,1),(-8:ℚ)),((0,2,2),(6:ℚ)),((0,5,0),(-8/3:ℚ)),((1,0,3),(-20/3:ℚ)),((1,3,1),(-64/3:ℚ)),((2,1,2),(8:ℚ)),((2,4,0),(52/3:ℚ)),((3,2,1),(64/3:ℚ)),((4,0,2),(-14/3:ℚ)),((4,3,0),(-68/3:ℚ)),((5,1,1),(-8:ℚ)),((6,2,0),(38/3:ℚ)),((7,0,1),(4/3:ℚ)),((8,1,0),(-10/3:ℚ)),((10,0,0),(1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,0,2),(-15:ℤ)),((0,3,0),(10:ℤ)),((1,1,1),(60:ℤ)),((2,2,0),(-45:ℤ)),((3,0,1),(-30:ℤ)),((4,1,0),(30:ℤ)),((6,0,0),(-5:ℤ)),((0,1,2),(-14:ℤ)),((0,4,0),(26:ℤ)),((1,2,1),(96:ℤ)),((2,0,2),(-33:ℤ)),((2,3,0),(-100:ℤ)),((3,1,1),(-56:ℤ)),((4,2,0),(89:ℤ)),((5,0,1),(14:ℤ)),((6,1,0),(-32:ℤ)),((8,0,0),(4:ℤ)),((0,0,3),(-72:ℤ)),((0,3,1),(48:ℤ)),((1,1,2),(288:ℤ)),((2,2,1),(-216:ℤ)),((3,0,2),(-144:ℤ)),((4,1,1),(144:ℤ)),((6,0,1),(-24:ℤ)),((0,2,2),(18:ℤ)),((0,5,0),(-8:ℤ)),((1,0,3),(-20:ℤ)),((1,3,1),(-64:ℤ)),((2,1,2),(24:ℤ)),((2,4,0),(52:ℤ)),((3,2,1),(64:ℤ)),((4,0,2),(-14:ℤ)),((4,3,0),(-68:ℤ)),((5,1,1),(-24:ℤ)),((6,2,0),(38:ℤ)),((7,0,1),(4:ℤ)),((8,1,0),(-10:ℤ)),((10,0,0),(1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,2),(-15:ℤ)),((0,3,0),(10:ℤ)),((1,1,1),(60:ℤ)),((2,2,0),(-45:ℤ)),((3,0,1),(-30:ℤ)),((4,1,0),(30:ℤ)),((6,0,0),(-5:ℤ)),((0,1,2),(-14:ℤ)),((0,4,0),(26:ℤ)),((1,2,1),(96:ℤ)),((2,0,2),(-33:ℤ)),((2,3,0),(-100:ℤ)),((3,1,1),(-56:ℤ)),((4,2,0),(89:ℤ)),((5,0,1),(14:ℤ)),((6,1,0),(-32:ℤ)),((8,0,0),(4:ℤ)),((0,0,3),(-72:ℤ)),((0,3,1),(48:ℤ)),((1,1,2),(288:ℤ)),((2,2,1),(-216:ℤ)),((3,0,2),(-144:ℤ)),((4,1,1),(144:ℤ)),((6,0,1),(-24:ℤ)),((0,2,2),(18:ℤ)),((0,5,0),(-8:ℤ)),((1,0,3),(-20:ℤ)),((1,3,1),(-64:ℤ)),((2,1,2),(24:ℤ)),((2,4,0),(52:ℤ)),((3,2,1),(64:ℤ)),((4,0,2),(-14:ℤ)),((4,3,0),(-68:ℤ)),((5,1,1),(-24:ℤ)),((6,2,0),(38:ℤ)),((7,0,1),(4:ℤ)),((8,1,0),(-10:ℤ)),((10,0,0),(1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 2 0 6 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_6
