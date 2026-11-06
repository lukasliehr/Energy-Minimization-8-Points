import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_4_8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,2,0),(2/3:ℚ)),((1,0,1),(4/3:ℚ)),((2,1,0),(-4/3:ℚ)),((4,0,0),(1/3:ℚ)),((0,1,2),(-8/3:ℚ)),((0,4,0),(2/3:ℚ)),((1,2,1),(8:ℚ)),((2,0,2),(4:ℚ)),((2,3,0),(-16/3:ℚ)),((3,1,1),(-32/3:ℚ)),((4,2,0),(20/3:ℚ)),((5,0,1),(8/3:ℚ)),((6,1,0),(-8/3:ℚ)),((8,0,0),(1/3:ℚ)),((0,0,4),(-2:ℚ)),((0,6,0),(8/3:ℚ)),((1,4,1),(16:ℚ)),((2,2,2),(32:ℚ)),((2,5,0),(-16:ℚ)),((3,0,3),(64/3:ℚ)),((3,3,1),(-64:ℚ)),((4,1,2),(-64:ℚ)),((4,4,0),(36:ℚ)),((5,2,1),(80:ℚ)),((6,0,2),(16:ℚ)),((6,3,0),(-112/3:ℚ)),((7,1,1),(-32:ℚ)),((8,2,0),(18:ℚ)),((9,0,1),(4:ℚ)),((10,1,0),(-4:ℚ)),((12,0,0),(1/3:ℚ))]
def raw16 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,2,0),(14:ℤ)),((1,0,1),(28:ℤ)),((2,1,0),(-28:ℤ)),((4,0,0),(7:ℤ)),((0,1,2),(-56:ℤ)),((0,4,0),(14:ℤ)),((1,2,1),(168:ℤ)),((2,0,2),(84:ℤ)),((2,3,0),(-112:ℤ)),((3,1,1),(-224:ℤ)),((4,2,0),(140:ℤ)),((5,0,1),(56:ℤ)),((6,1,0),(-56:ℤ)),((8,0,0),(7:ℤ)),((0,0,4),(-42:ℤ)),((0,6,0),(56:ℤ)),((1,4,1),(336:ℤ)),((2,2,2),(672:ℤ)),((2,5,0),(-336:ℤ)),((3,0,3),(448:ℤ)),((3,3,1),(-1344:ℤ)),((4,1,2),(-1344:ℤ)),((4,4,0),(756:ℤ)),((5,2,1),(1680:ℤ)),((6,0,2),(336:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator16 : ℕ := 21
theorem normalize_16 : raw16.map (fun x => (x.1, (x.2:ℚ)/denominator16))=entry := by norm_num [raw16,denominator16,entry]
theorem denominator_16_positive : 0<denominator16 := by decide
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,2,0),(14:ℤ)),((1,0,1),(28:ℤ)),((2,1,0),(-28:ℤ)),((4,0,0),(7:ℤ)),((0,1,2),(-56:ℤ)),((0,4,0),(14:ℤ)),((1,2,1),(168:ℤ)),((2,0,2),(84:ℤ)),((2,3,0),(-112:ℤ)),((3,1,1),(-224:ℤ)),((4,2,0),(140:ℤ)),((5,0,1),(56:ℤ)),((6,1,0),(-56:ℤ)),((8,0,0),(7:ℤ)),((0,0,4),(-42:ℤ)),((0,6,0),(56:ℤ)),((1,4,1),(336:ℤ)),((2,2,2),(672:ℤ)),((2,5,0),(-336:ℤ)),((3,0,3),(448:ℤ)),((3,3,1),(-1344:ℤ)),((4,1,2),(-1344:ℤ)),((4,4,0),(756:ℤ)),((5,2,1),(1680:ℤ)),((6,0,2),(336:ℤ)),((6,3,0),(-784:ℤ)),((7,1,1),(-672:ℤ)),((8,2,0),(378:ℤ)),((9,0,1),(84:ℤ)),((10,1,0),(-84:ℤ)),((12,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 4 8 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_4_8
