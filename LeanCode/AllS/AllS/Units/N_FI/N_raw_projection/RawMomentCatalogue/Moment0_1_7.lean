import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_1_7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((1,0,0),(1/3:ℚ)),((0,2,1),(7/3:ℚ)),((1,0,2),(7/3:ℚ)),((1,3,0),(-7/3:ℚ)),((2,1,1),(-7:ℚ)),((3,2,0),(14/3:ℚ)),((4,0,1),(7/3:ℚ)),((5,1,0),(-7/3:ℚ)),((7,0,0),(1/3:ℚ)),((0,1,2),(16/3:ℚ)),((0,4,0),(-4/3:ℚ)),((1,2,1),(-9:ℚ)),((2,0,2),(-1:ℚ)),((2,3,0),(11/3:ℚ)),((3,1,1),(1/3:ℚ)),((4,2,0),(2/3:ℚ)),((5,0,1),(5/3:ℚ)),((6,1,0),(-5/3:ℚ)),((8,0,0),(1/3:ℚ))]
def raw14 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((1,0,0),(7:ℤ)),((0,2,1),(49:ℤ)),((1,0,2),(49:ℤ)),((1,3,0),(-49:ℤ)),((2,1,1),(-147:ℤ)),((3,2,0),(98:ℤ)),((4,0,1),(49:ℤ)),((5,1,0),(-49:ℤ)),((7,0,0),(7:ℤ)),((0,1,2),(112:ℤ)),((0,4,0),(-28:ℤ)),((1,2,1),(-189:ℤ)),((2,0,2),(-21:ℤ)),((2,3,0),(77:ℤ)),((3,1,1),(7:ℤ)),((4,2,0),(14:ℤ)),((5,0,1),(35:ℤ)),((6,1,0),(-35:ℤ)),((8,0,0),(7:ℤ))]
def denominator14 : ℕ := 21
theorem normalize_14 : raw14.map (fun x => (x.1, (x.2:ℚ)/denominator14))=entry := by norm_num [raw14,denominator14,entry]
theorem denominator_14_positive : 0<denominator14 := by decide
def raw16 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((1,0,0),(7:ℤ)),((0,2,1),(49:ℤ)),((1,0,2),(49:ℤ)),((1,3,0),(-49:ℤ)),((2,1,1),(-147:ℤ)),((3,2,0),(98:ℤ)),((4,0,1),(49:ℤ)),((5,1,0),(-49:ℤ)),((7,0,0),(7:ℤ)),((0,1,2),(112:ℤ)),((0,4,0),(-28:ℤ)),((1,2,1),(-189:ℤ)),((2,0,2),(-21:ℤ)),((2,3,0),(77:ℤ)),((3,1,1),(7:ℤ)),((4,2,0),(14:ℤ)),((5,0,1),(35:ℤ)),((6,1,0),(-35:ℤ)),((8,0,0),(7:ℤ))]
def denominator16 : ℕ := 21
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((1,0,0),(7:ℤ)),((0,2,1),(49:ℤ)),((1,0,2),(49:ℤ)),((1,3,0),(-49:ℤ)),((2,1,1),(-147:ℤ)),((3,2,0),(98:ℤ)),((4,0,1),(49:ℤ)),((5,1,0),(-49:ℤ)),((7,0,0),(7:ℤ)),((0,1,2),(112:ℤ)),((0,4,0),(-28:ℤ)),((1,2,1),(-189:ℤ)),((2,0,2),(-21:ℤ)),((2,3,0),(77:ℤ)),((3,1,1),(7:ℤ)),((4,2,0),(14:ℤ)),((5,0,1),(35:ℤ)),((6,1,0),(-35:ℤ)),((8,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 1 7 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_1_7
