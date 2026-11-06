import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_1
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((1,0,0),(-5/3:ℚ)),((0,0,1),(-5:ℚ)),((1,1,0),(-1:ℚ)),((3,0,0),(4/3:ℚ)),((1,0,1),(-8:ℚ)),((0,1,1),(-8/3:ℚ)),((1,2,0),(8/3:ℚ)),((2,0,1),(-1/3:ℚ)),((3,1,0),(-5/3:ℚ)),((5,0,0),(1/3:ℚ))]
def raw12 : List (Tag × ℤ) := [((1,0,0),(-5:ℤ)),((0,0,1),(-15:ℤ)),((1,1,0),(-3:ℤ)),((3,0,0),(4:ℤ)),((1,0,1),(-24:ℤ)),((0,1,1),(-8:ℤ)),((1,2,0),(8:ℤ)),((2,0,1),(-1:ℤ)),((3,1,0),(-5:ℤ)),((5,0,0),(1:ℤ))]
def denominator12 : ℕ := 3
theorem normalize_12 : raw12.map (fun x => (x.1, (x.2:ℚ)/denominator12))=entry := by norm_num [raw12,denominator12,entry]
theorem denominator_12_positive : 0<denominator12 := by decide
def raw14 : List (Tag × ℤ) := [((1,0,0),(-5:ℤ)),((0,0,1),(-15:ℤ)),((1,1,0),(-3:ℤ)),((3,0,0),(4:ℤ)),((1,0,1),(-24:ℤ)),((0,1,1),(-8:ℤ)),((1,2,0),(8:ℤ)),((2,0,1),(-1:ℤ)),((3,1,0),(-5:ℤ)),((5,0,0),(1:ℤ))]
def denominator14 : ℕ := 3
theorem normalize_14 : raw14.map (fun x => (x.1, (x.2:ℚ)/denominator14))=entry := by norm_num [raw14,denominator14,entry]
theorem denominator_14_positive : 0<denominator14 := by decide
def raw16 : List (Tag × ℤ) := [((1,0,0),(-5:ℤ)),((0,0,1),(-15:ℤ)),((1,1,0),(-3:ℤ)),((3,0,0),(4:ℤ)),((1,0,1),(-24:ℤ)),((0,1,1),(-8:ℤ)),((1,2,0),(8:ℤ)),((2,0,1),(-1:ℤ)),((3,1,0),(-5:ℤ)),((5,0,0),(1:ℤ))]
def denominator16 : ℕ := 3
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((1,0,0),(-5:ℤ)),((0,0,1),(-15:ℤ)),((1,1,0),(-3:ℤ)),((3,0,0),(4:ℤ)),((1,0,1),(-24:ℤ)),((0,1,1),(-8:ℤ)),((1,2,0),(8:ℤ)),((2,0,1),(-1:ℤ)),((3,1,0),(-5:ℤ)),((5,0,0),(1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 2 0 1 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_1
