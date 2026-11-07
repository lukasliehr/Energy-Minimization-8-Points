import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_4_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,2,0),(2/3:ℚ)),((1,0,1),(4/3:ℚ)),((2,1,0),(-4/3:ℚ)),((4,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,2,3),(-34/3:ℚ)),((0,5,1),(-28/3:ℚ)),((1,0,4),(10/3:ℚ)),((1,3,2),(-10/3:ℚ)),((1,6,0),(28/3:ℚ)),((2,1,3),(-100/3:ℚ)),((2,4,1),(50:ℚ)),((3,2,2),(100:ℚ)),((3,5,0),(-106/3:ℚ)),((4,0,3),(95/3:ℚ)),((4,3,1),(-395/3:ℚ)),((5,1,2),(-97:ℚ)),((5,4,0),(185/3:ℚ)),((6,2,1),(352/3:ℚ)),((7,0,2),(58/3:ℚ)),((7,3,0),(-52:ℚ)),((8,1,1),(-39:ℚ)),((9,2,0),(65/3:ℚ)),((10,0,1),(13/3:ℚ)),((11,1,0),(-13/3:ℚ)),((13,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,2,0),(14:ℤ)),((1,0,1),(28:ℤ)),((2,1,0),(-28:ℤ)),((4,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,2,3),(-238:ℤ)),((0,5,1),(-196:ℤ)),((1,0,4),(70:ℤ)),((1,3,2),(-70:ℤ)),((1,6,0),(196:ℤ)),((2,1,3),(-700:ℤ)),((2,4,1),(1050:ℤ)),((3,2,2),(2100:ℤ)),((3,5,0),(-742:ℤ)),((4,0,3),(665:ℤ)),((4,3,1),(-2765:ℤ)),((5,1,2),(-2037:ℤ)),((5,4,0),(1295:ℤ)),((6,2,1),(2464:ℤ)),((7,0,2),(406:ℤ)),((7,3,0),(-1092:ℤ)),((8,1,1),(-819:ℤ)),((9,2,0),(455:ℤ)),((10,0,1),(91:ℤ)),((11,1,0),(-91:ℤ)),((13,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 4 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_4_9
