import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_2_7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,2,2),(-7:ℚ)),((1,0,3),(-4:ℚ)),((1,3,1),(5:ℚ)),((2,1,2),(9:ℚ)),((3,2,1),(-5:ℚ)),((4,0,2),(-1:ℚ)),((5,1,1),(1:ℚ)),((0,1,3),(50/3:ℚ)),((0,4,1),(4/3:ℚ)),((1,2,2),(-52:ℚ)),((1,5,0),(-4/3:ℚ)),((2,0,3),(-64/3:ℚ)),((2,3,1),(140/3:ℚ)),((3,1,2),(200/3:ℚ)),((3,4,0),(-40/3:ℚ)),((4,2,1),(-70:ℚ)),((5,0,2),(-14:ℚ)),((5,3,0),(74/3:ℚ)),((6,1,1),(86/3:ℚ)),((7,2,0),(-44/3:ℚ)),((8,0,1),(-11/3:ℚ)),((9,1,0),(11/3:ℚ)),((11,0,0),(-1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,0,3),(3:ℤ)),((0,3,1),(-9:ℤ)),((1,1,2),(-27:ℤ)),((1,4,0),(9:ℤ)),((2,2,1),(54:ℤ)),((3,0,2),(18:ℤ)),((3,3,0),(-30:ℤ)),((4,1,1),(-45:ℤ)),((5,2,0),(27:ℤ)),((6,0,1),(9:ℤ)),((7,1,0),(-9:ℤ)),((9,0,0),(1:ℤ)),((0,2,2),(-21:ℤ)),((1,0,3),(-12:ℤ)),((1,3,1),(15:ℤ)),((2,1,2),(27:ℤ)),((3,2,1),(-15:ℤ)),((4,0,2),(-3:ℤ)),((5,1,1),(3:ℤ)),((0,1,3),(50:ℤ)),((0,4,1),(4:ℤ)),((1,2,2),(-156:ℤ)),((1,5,0),(-4:ℤ)),((2,0,3),(-64:ℤ)),((2,3,1),(140:ℤ)),((3,1,2),(200:ℤ)),((3,4,0),(-40:ℤ)),((4,2,1),(-210:ℤ)),((5,0,2),(-42:ℤ)),((5,3,0),(74:ℤ)),((6,1,1),(86:ℤ)),((7,2,0),(-44:ℤ)),((8,0,1),(-11:ℤ)),((9,1,0),(11:ℤ)),((11,0,0),(-1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,3),(3:ℤ)),((0,3,1),(-9:ℤ)),((1,1,2),(-27:ℤ)),((1,4,0),(9:ℤ)),((2,2,1),(54:ℤ)),((3,0,2),(18:ℤ)),((3,3,0),(-30:ℤ)),((4,1,1),(-45:ℤ)),((5,2,0),(27:ℤ)),((6,0,1),(9:ℤ)),((7,1,0),(-9:ℤ)),((9,0,0),(1:ℤ)),((0,2,2),(-21:ℤ)),((1,0,3),(-12:ℤ)),((1,3,1),(15:ℤ)),((2,1,2),(27:ℤ)),((3,2,1),(-15:ℤ)),((4,0,2),(-3:ℤ)),((5,1,1),(3:ℤ)),((0,1,3),(50:ℤ)),((0,4,1),(4:ℤ)),((1,2,2),(-156:ℤ)),((1,5,0),(-4:ℤ)),((2,0,3),(-64:ℤ)),((2,3,1),(140:ℤ)),((3,1,2),(200:ℤ)),((3,4,0),(-40:ℤ)),((4,2,1),(-210:ℤ)),((5,0,2),(-42:ℤ)),((5,3,0),(74:ℤ)),((6,1,1),(86:ℤ)),((7,2,0),(-44:ℤ)),((8,0,1),(-11:ℤ)),((9,1,0),(11:ℤ)),((11,0,0),(-1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 1 2 7 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment1_2_7
