import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_0_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(8/7:ℚ)),((0,0,3),(8:ℚ)),((0,3,1),(-24:ℚ)),((1,1,2),(-72:ℚ)),((1,4,0),(24:ℚ)),((2,2,1),(144:ℚ)),((3,0,2),(48:ℚ)),((3,3,0),(-80:ℚ)),((4,1,1),(-120:ℚ)),((5,2,0),(72:ℚ)),((6,0,1),(24:ℚ)),((7,1,0),(-24:ℚ)),((9,0,0),(8/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(24:ℤ)),((0,0,3),(168:ℤ)),((0,3,1),(-504:ℤ)),((1,1,2),(-1512:ℤ)),((1,4,0),(504:ℤ)),((2,2,1),(3024:ℤ)),((3,0,2),(1008:ℤ)),((3,3,0),(-1680:ℤ)),((4,1,1),(-2520:ℤ)),((5,2,0),(1512:ℤ)),((6,0,1),(504:ℤ)),((7,1,0),(-504:ℤ)),((9,0,0),(56:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 0 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_0_9
