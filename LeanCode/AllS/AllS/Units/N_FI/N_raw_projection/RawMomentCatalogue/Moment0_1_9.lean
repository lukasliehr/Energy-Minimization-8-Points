import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_1_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((1,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,2,2),(-10:ℚ)),((0,5,0),(4/3:ℚ)),((1,0,3),(-11/3:ℚ)),((1,3,1),(53/3:ℚ)),((2,1,2),(13:ℚ)),((2,4,0),(-23/3:ℚ)),((3,2,1),(-38/3:ℚ)),((4,0,2),(4/3:ℚ)),((4,3,0),(10/3:ℚ)),((5,1,1),(-5:ℚ)),((6,2,0),(11/3:ℚ)),((7,0,1),(7/3:ℚ)),((8,1,0),(-7/3:ℚ)),((10,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((1,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,2,2),(-210:ℤ)),((0,5,0),(28:ℤ)),((1,0,3),(-77:ℤ)),((1,3,1),(371:ℤ)),((2,1,2),(273:ℤ)),((2,4,0),(-161:ℤ)),((3,2,1),(-266:ℤ)),((4,0,2),(28:ℤ)),((4,3,0),(70:ℤ)),((5,1,1),(-105:ℤ)),((6,2,0),(77:ℤ)),((7,0,1),(49:ℤ)),((8,1,0),(-49:ℤ)),((10,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 1 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_1_9
