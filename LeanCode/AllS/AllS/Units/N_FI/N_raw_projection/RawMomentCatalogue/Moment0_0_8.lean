import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_0_8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(8/7:ℚ)),((0,1,2),(-64/3:ℚ)),((0,4,0),(16/3:ℚ)),((1,2,1),(64:ℚ)),((2,0,2),(32:ℚ)),((2,3,0),(-128/3:ℚ)),((3,1,1),(-256/3:ℚ)),((4,2,0),(160/3:ℚ)),((5,0,1),(64/3:ℚ)),((6,1,0),(-64/3:ℚ)),((8,0,0),(8/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,0,0),(24:ℤ)),((0,1,2),(-448:ℤ)),((0,4,0),(112:ℤ)),((1,2,1),(1344:ℤ)),((2,0,2),(672:ℤ)),((2,3,0),(-896:ℤ)),((3,1,1),(-1792:ℤ)),((4,2,0),(1120:ℤ)),((5,0,1),(448:ℤ)),((6,1,0),(-448:ℤ)),((8,0,0),(56:ℤ))]
def denominator16 : ℕ := 21
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,0),(24:ℤ)),((0,1,2),(-448:ℤ)),((0,4,0),(112:ℤ)),((1,2,1),(1344:ℤ)),((2,0,2),(672:ℤ)),((2,3,0),(-896:ℤ)),((3,1,1),(-1792:ℤ)),((4,2,0),(1120:ℤ)),((5,0,1),(448:ℤ)),((6,1,0),(-448:ℤ)),((8,0,0),(56:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 0 8 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_0_8
