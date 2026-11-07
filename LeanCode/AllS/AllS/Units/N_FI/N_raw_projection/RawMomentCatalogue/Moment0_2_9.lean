import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_2_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,1,0),(-2/3:ℚ)),((2,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,1,3),(4/3:ℚ)),((0,4,1),(32/3:ℚ)),((1,2,2),(10:ℚ)),((1,5,0),(-32/3:ℚ)),((2,0,3),(-35/3:ℚ)),((2,3,1),(-131/3:ℚ)),((3,1,2),(31/3:ℚ)),((3,4,0),(97/3:ℚ)),((4,2,1),(34:ℚ)),((5,0,2),(-4:ℚ)),((5,3,0),(-98/3:ℚ)),((6,1,1),(-35/3:ℚ)),((7,2,0),(47/3:ℚ)),((8,0,1),(5/3:ℚ)),((9,1,0),(-11/3:ℚ)),((11,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,1,0),(-14:ℤ)),((2,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,1,3),(28:ℤ)),((0,4,1),(224:ℤ)),((1,2,2),(210:ℤ)),((1,5,0),(-224:ℤ)),((2,0,3),(-245:ℤ)),((2,3,1),(-917:ℤ)),((3,1,2),(217:ℤ)),((3,4,0),(679:ℤ)),((4,2,1),(714:ℤ)),((5,0,2),(-84:ℤ)),((5,3,0),(-686:ℤ)),((6,1,1),(-245:ℤ)),((7,2,0),(329:ℤ)),((8,0,1),(35:ℤ)),((9,1,0),(-77:ℤ)),((11,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 2 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_2_9
