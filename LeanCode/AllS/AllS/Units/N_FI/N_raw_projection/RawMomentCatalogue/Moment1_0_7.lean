import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_0_7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,2,1),(7/3:ℚ)),((1,0,2),(7/3:ℚ)),((1,3,0),(-7/3:ℚ)),((2,1,1),(-7:ℚ)),((3,2,0),(14/3:ℚ)),((4,0,1),(7/3:ℚ)),((5,1,0),(-7/3:ℚ)),((7,0,0),(1/3:ℚ)),((0,1,2),(8:ℚ)),((0,4,0),(-2:ℚ)),((1,2,1),(-17:ℚ)),((2,0,2),(-5:ℚ)),((2,3,0),(9:ℚ)),((3,1,1),(11:ℚ)),((4,2,0),(-6:ℚ)),((5,0,1),(-1:ℚ)),((6,1,0),(1:ℚ)),((0,0,3),(2:ℚ)),((0,3,1),(-6:ℚ)),((1,1,2),(-10:ℚ)),((1,4,0),(4:ℚ)),((2,2,1),(12:ℚ)),((3,3,0),(-4:ℚ)),((4,1,1),(2:ℚ)),((5,2,0),(-2:ℚ)),((6,0,1),(-2:ℚ)),((7,1,0),(2:ℚ)),((9,0,0),(-1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,2,1),(7:ℤ)),((1,0,2),(7:ℤ)),((1,3,0),(-7:ℤ)),((2,1,1),(-21:ℤ)),((3,2,0),(14:ℤ)),((4,0,1),(7:ℤ)),((5,1,0),(-7:ℤ)),((7,0,0),(1:ℤ)),((0,1,2),(24:ℤ)),((0,4,0),(-6:ℤ)),((1,2,1),(-51:ℤ)),((2,0,2),(-15:ℤ)),((2,3,0),(27:ℤ)),((3,1,1),(33:ℤ)),((4,2,0),(-18:ℤ)),((5,0,1),(-3:ℤ)),((6,1,0),(3:ℤ)),((0,0,3),(6:ℤ)),((0,3,1),(-18:ℤ)),((1,1,2),(-30:ℤ)),((1,4,0),(12:ℤ)),((2,2,1),(36:ℤ)),((3,3,0),(-12:ℤ)),((4,1,1),(6:ℤ)),((5,2,0),(-6:ℤ)),((6,0,1),(-6:ℤ)),((7,1,0),(6:ℤ)),((9,0,0),(-1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,2,1),(7:ℤ)),((1,0,2),(7:ℤ)),((1,3,0),(-7:ℤ)),((2,1,1),(-21:ℤ)),((3,2,0),(14:ℤ)),((4,0,1),(7:ℤ)),((5,1,0),(-7:ℤ)),((7,0,0),(1:ℤ)),((0,1,2),(24:ℤ)),((0,4,0),(-6:ℤ)),((1,2,1),(-51:ℤ)),((2,0,2),(-15:ℤ)),((2,3,0),(27:ℤ)),((3,1,1),(33:ℤ)),((4,2,0),(-18:ℤ)),((5,0,1),(-3:ℤ)),((6,1,0),(3:ℤ)),((0,0,3),(6:ℤ)),((0,3,1),(-18:ℤ)),((1,1,2),(-30:ℤ)),((1,4,0),(12:ℤ)),((2,2,1),(36:ℤ)),((3,3,0),(-12:ℤ)),((4,1,1),(6:ℤ)),((5,2,0),(-6:ℤ)),((6,0,1),(-6:ℤ)),((7,1,0),(6:ℤ)),((9,0,0),(-1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 1 0 7 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_0_7
