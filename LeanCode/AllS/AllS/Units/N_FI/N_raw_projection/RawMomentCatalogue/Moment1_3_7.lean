import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_3_7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,2,2),(5:ℚ)),((0,5,0),(-2/3:ℚ)),((1,0,3),(10/3:ℚ)),((1,3,1),(-40/3:ℚ)),((2,1,2),(-20:ℚ)),((2,4,0),(25/3:ℚ)),((3,2,1),(100/3:ℚ)),((4,0,2),(25/3:ℚ)),((4,3,0),(-50/3:ℚ)),((5,1,1),(-20:ℚ)),((6,2,0),(35/3:ℚ)),((7,0,1),(10/3:ℚ)),((8,1,0),(-10/3:ℚ)),((10,0,0),(1/3:ℚ)),((0,1,3),(2:ℚ)),((0,4,1),(2:ℚ)),((2,0,3),(-9:ℚ)),((2,3,1),(-4:ℚ)),((3,1,2),(8:ℚ)),((4,2,1),(1:ℚ)),((5,0,2),(-2:ℚ)),((0,0,4),(2:ℚ)),((0,6,0),(-8/3:ℚ)),((1,4,1),(-16:ℚ)),((2,2,2),(-32:ℚ)),((2,5,0),(16:ℚ)),((3,0,3),(-64/3:ℚ)),((3,3,1),(64:ℚ)),((4,1,2),(64:ℚ)),((4,4,0),(-36:ℚ)),((5,2,1),(-80:ℚ)),((6,0,2),(-16:ℚ)),((6,3,0),(112/3:ℚ)),((7,1,1),(32:ℚ)),((8,2,0),(-18:ℚ)),((9,0,1),(-4:ℚ)),((10,1,0),(4:ℚ)),((12,0,0),(-1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,2,2),(15:ℤ)),((0,5,0),(-2:ℤ)),((1,0,3),(10:ℤ)),((1,3,1),(-40:ℤ)),((2,1,2),(-60:ℤ)),((2,4,0),(25:ℤ)),((3,2,1),(100:ℤ)),((4,0,2),(25:ℤ)),((4,3,0),(-50:ℤ)),((5,1,1),(-60:ℤ)),((6,2,0),(35:ℤ)),((7,0,1),(10:ℤ)),((8,1,0),(-10:ℤ)),((10,0,0),(1:ℤ)),((0,1,3),(6:ℤ)),((0,4,1),(6:ℤ)),((2,0,3),(-27:ℤ)),((2,3,1),(-12:ℤ)),((3,1,2),(24:ℤ)),((4,2,1),(3:ℤ)),((5,0,2),(-6:ℤ)),((0,0,4),(6:ℤ)),((0,6,0),(-8:ℤ)),((1,4,1),(-48:ℤ)),((2,2,2),(-96:ℤ)),((2,5,0),(48:ℤ)),((3,0,3),(-64:ℤ)),((3,3,1),(192:ℤ)),((4,1,2),(192:ℤ)),((4,4,0),(-108:ℤ)),((5,2,1),(-240:ℤ)),((6,0,2),(-48:ℤ)),((6,3,0),(112:ℤ)),((7,1,1),(96:ℤ)),((8,2,0),(-54:ℤ)),((9,0,1),(-12:ℤ)),((10,1,0),(12:ℤ)),((12,0,0),(-1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,2,2),(15:ℤ)),((0,5,0),(-2:ℤ)),((1,0,3),(10:ℤ)),((1,3,1),(-40:ℤ)),((2,1,2),(-60:ℤ)),((2,4,0),(25:ℤ)),((3,2,1),(100:ℤ)),((4,0,2),(25:ℤ)),((4,3,0),(-50:ℤ)),((5,1,1),(-60:ℤ)),((6,2,0),(35:ℤ)),((7,0,1),(10:ℤ)),((8,1,0),(-10:ℤ)),((10,0,0),(1:ℤ)),((0,1,3),(6:ℤ)),((0,4,1),(6:ℤ)),((2,0,3),(-27:ℤ)),((2,3,1),(-12:ℤ)),((3,1,2),(24:ℤ)),((4,2,1),(3:ℤ)),((5,0,2),(-6:ℤ)),((0,0,4),(6:ℤ)),((0,6,0),(-8:ℤ)),((1,4,1),(-48:ℤ)),((2,2,2),(-96:ℤ)),((2,5,0),(48:ℤ)),((3,0,3),(-64:ℤ)),((3,3,1),(192:ℤ)),((4,1,2),(192:ℤ)),((4,4,0),(-108:ℤ)),((5,2,1),(-240:ℤ)),((6,0,2),(-48:ℤ)),((6,3,0),(112:ℤ)),((7,1,1),(96:ℤ)),((8,2,0),(-54:ℤ)),((9,0,1),(-12:ℤ)),((10,1,0),(12:ℤ)),((12,0,0),(-1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 1 3 7 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_3_7
