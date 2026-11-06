import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_2_6
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,1,2),(-8/3:ℚ)),((0,4,0),(2/3:ℚ)),((1,2,1),(8:ℚ)),((2,0,2),(4:ℚ)),((2,3,0),(-16/3:ℚ)),((3,1,1),(-32/3:ℚ)),((4,2,0),(20/3:ℚ)),((5,0,1),(8/3:ℚ)),((6,1,0),(-8/3:ℚ)),((8,0,0),(1/3:ℚ)),((0,0,3),(-3:ℚ)),((0,3,1),(2:ℚ)),((1,1,2),(7:ℚ)),((2,2,1),(-4:ℚ)),((3,0,2),(-1:ℚ)),((4,1,1),(1:ℚ)),((0,2,2),(-11:ℚ)),((0,5,0),(-4/3:ℚ)),((1,0,3),(-43/3:ℚ)),((1,3,1),(46/3:ℚ)),((2,1,2),(44:ℚ)),((2,4,0),(-13/3:ℚ)),((3,2,1),(-136/3:ℚ)),((4,0,2),(-34/3:ℚ)),((4,3,0),(47/3:ℚ)),((5,1,1),(23:ℚ)),((6,2,0),(-35/3:ℚ)),((7,0,1),(-10/3:ℚ)),((8,1,0),(10/3:ℚ)),((10,0,0),(-1/3:ℚ))]
def raw14 : List (Tag × ℤ) := [((0,1,2),(-8:ℤ)),((0,4,0),(2:ℤ)),((1,2,1),(24:ℤ)),((2,0,2),(12:ℤ)),((2,3,0),(-16:ℤ)),((3,1,1),(-32:ℤ)),((4,2,0),(20:ℤ)),((5,0,1),(8:ℤ)),((6,1,0),(-8:ℤ)),((8,0,0),(1:ℤ)),((0,0,3),(-9:ℤ)),((0,3,1),(6:ℤ)),((1,1,2),(21:ℤ)),((2,2,1),(-12:ℤ)),((3,0,2),(-3:ℤ)),((4,1,1),(3:ℤ)),((0,2,2),(-33:ℤ)),((0,5,0),(-4:ℤ)),((1,0,3),(-43:ℤ)),((1,3,1),(46:ℤ)),((2,1,2),(132:ℤ)),((2,4,0),(-13:ℤ)),((3,2,1),(-136:ℤ)),((4,0,2),(-34:ℤ)),((4,3,0),(47:ℤ)),((5,1,1),(69:ℤ)),((6,2,0),(-35:ℤ)),((7,0,1),(-10:ℤ)),((8,1,0),(10:ℤ)),((10,0,0),(-1:ℤ))]
def denominator14 : ℕ := 3
theorem normalize_14 : raw14.map (fun x => (x.1, (x.2:ℚ)/denominator14))=entry := by norm_num [raw14,denominator14,entry]
theorem denominator_14_positive : 0<denominator14 := by decide
def raw16 : List (Tag × ℤ) := [((0,1,2),(-8:ℤ)),((0,4,0),(2:ℤ)),((1,2,1),(24:ℤ)),((2,0,2),(12:ℤ)),((2,3,0),(-16:ℤ)),((3,1,1),(-32:ℤ)),((4,2,0),(20:ℤ)),((5,0,1),(8:ℤ)),((6,1,0),(-8:ℤ)),((8,0,0),(1:ℤ)),((0,0,3),(-9:ℤ)),((0,3,1),(6:ℤ)),((1,1,2),(21:ℤ)),((2,2,1),(-12:ℤ)),((3,0,2),(-3:ℤ)),((4,1,1),(3:ℤ)),((0,2,2),(-33:ℤ)),((0,5,0),(-4:ℤ)),((1,0,3),(-43:ℤ)),((1,3,1),(46:ℤ)),((2,1,2),(132:ℤ)),((2,4,0),(-13:ℤ)),((3,2,1),(-136:ℤ)),((4,0,2),(-34:ℤ)),((4,3,0),(47:ℤ)),((5,1,1),(69:ℤ)),((6,2,0),(-35:ℤ)),((7,0,1),(-10:ℤ)),((8,1,0),(10:ℤ)),((10,0,0),(-1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,1,2),(-8:ℤ)),((0,4,0),(2:ℤ)),((1,2,1),(24:ℤ)),((2,0,2),(12:ℤ)),((2,3,0),(-16:ℤ)),((3,1,1),(-32:ℤ)),((4,2,0),(20:ℤ)),((5,0,1),(8:ℤ)),((6,1,0),(-8:ℤ)),((8,0,0),(1:ℤ)),((0,0,3),(-9:ℤ)),((0,3,1),(6:ℤ)),((1,1,2),(21:ℤ)),((2,2,1),(-12:ℤ)),((3,0,2),(-3:ℤ)),((4,1,1),(3:ℤ)),((0,2,2),(-33:ℤ)),((0,5,0),(-4:ℤ)),((1,0,3),(-43:ℤ)),((1,3,1),(46:ℤ)),((2,1,2),(132:ℤ)),((2,4,0),(-13:ℤ)),((3,2,1),(-136:ℤ)),((4,0,2),(-34:ℤ)),((4,3,0),(47:ℤ)),((5,1,1),(69:ℤ)),((6,2,0),(-35:ℤ)),((7,0,1),(-10:ℤ)),((8,1,0),(10:ℤ)),((10,0,0),(-1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 1 2 6 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_2_6
