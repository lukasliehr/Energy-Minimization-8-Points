import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_6_6
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,0,2),(2:ℚ)),((0,3,0),(-4/3:ℚ)),((1,1,1),(-8:ℚ)),((2,2,0),(6:ℚ)),((3,0,1),(4:ℚ)),((4,1,0),(-4:ℚ)),((6,0,0),(2/3:ℚ)),((0,0,4),(7:ℚ)),((0,3,2),(4:ℚ)),((0,6,0),(8/3:ℚ)),((1,1,3),(-40:ℚ)),((1,4,1),(8:ℚ)),((2,2,2),(78:ℚ)),((2,5,0),(-12:ℚ)),((3,0,3),(28/3:ℚ)),((3,3,1),(-80:ℚ)),((4,1,2),(-60:ℚ)),((4,4,0),(35:ℚ)),((5,2,1),(84:ℚ)),((6,0,2),(14:ℚ)),((6,3,0),(-112/3:ℚ)),((7,1,1),(-32:ℚ)),((8,2,0),(18:ℚ)),((9,0,1),(4:ℚ)),((10,1,0),(-4:ℚ)),((12,0,0),(1/3:ℚ))]
def raw12 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,2),(42:ℤ)),((0,3,0),(-28:ℤ)),((1,1,1),(-168:ℤ)),((2,2,0),(126:ℤ)),((3,0,1),(84:ℤ)),((4,1,0),(-84:ℤ)),((6,0,0),(14:ℤ)),((0,0,4),(147:ℤ)),((0,3,2),(84:ℤ)),((0,6,0),(56:ℤ)),((1,1,3),(-840:ℤ)),((1,4,1),(168:ℤ)),((2,2,2),(1638:ℤ)),((2,5,0),(-252:ℤ)),((3,0,3),(196:ℤ)),((3,3,1),(-1680:ℤ)),((4,1,2),(-1260:ℤ)),((4,4,0),(735:ℤ)),((5,2,1),(1764:ℤ)),((6,0,2),(294:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator12 : ℕ := 21
theorem normalize_12 : raw12.map (fun x => (x.1, (x.2:ℚ)/denominator12))=entry := by norm_num [raw12,denominator12,entry]
theorem denominator_12_positive : 0<denominator12 := by decide
def raw14 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,2),(42:ℤ)),((0,3,0),(-28:ℤ)),((1,1,1),(-168:ℤ)),((2,2,0),(126:ℤ)),((3,0,1),(84:ℤ)),((4,1,0),(-84:ℤ)),((6,0,0),(14:ℤ)),((0,0,4),(147:ℤ)),((0,3,2),(84:ℤ)),((0,6,0),(56:ℤ)),((1,1,3),(-840:ℤ)),((1,4,1),(168:ℤ)),((2,2,2),(1638:ℤ)),((2,5,0),(-252:ℤ)),((3,0,3),(196:ℤ)),((3,3,1),(-1680:ℤ)),((4,1,2),(-1260:ℤ)),((4,4,0),(735:ℤ)),((5,2,1),(1764:ℤ)),((6,0,2),(294:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator14 : ℕ := 21
theorem normalize_14 : raw14.map (fun x => (x.1, (x.2:ℚ)/denominator14))=entry := by norm_num [raw14,denominator14,entry]
theorem denominator_14_positive : 0<denominator14 := by decide
def raw16 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,2),(42:ℤ)),((0,3,0),(-28:ℤ)),((1,1,1),(-168:ℤ)),((2,2,0),(126:ℤ)),((3,0,1),(84:ℤ)),((4,1,0),(-84:ℤ)),((6,0,0),(14:ℤ)),((0,0,4),(147:ℤ)),((0,3,2),(84:ℤ)),((0,6,0),(56:ℤ)),((1,1,3),(-840:ℤ)),((1,4,1),(168:ℤ)),((2,2,2),(1638:ℤ)),((2,5,0),(-252:ℤ)),((3,0,3),(196:ℤ)),((3,3,1),(-1680:ℤ)),((4,1,2),(-1260:ℤ)),((4,4,0),(735:ℤ)),((5,2,1),(1764:ℤ)),((6,0,2),(294:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator16 : ℕ := 21
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,2),(42:ℤ)),((0,3,0),(-28:ℤ)),((1,1,1),(-168:ℤ)),((2,2,0),(126:ℤ)),((3,0,1),(84:ℤ)),((4,1,0),(-84:ℤ)),((6,0,0),(14:ℤ)),((0,0,4),(147:ℤ)),((0,3,2),(84:ℤ)),((0,6,0),(56:ℤ)),((1,1,3),(-840:ℤ)),((1,4,1),(168:ℤ)),((2,2,2),(1638:ℤ)),((2,5,0),(-252:ℤ)),((3,0,3),(196:ℤ)),((3,3,1),(-1680:ℤ)),((4,1,2),(-1260:ℤ)),((4,4,0),(735:ℤ)),((5,2,1),(1764:ℤ)),((6,0,2),(294:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 6 6 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_6_6
