import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_6_9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,0,0),(1/7:ℚ)),((0,0,2),(1:ℚ)),((0,3,0),(-2/3:ℚ)),((1,1,1),(-4:ℚ)),((2,2,0),(3:ℚ)),((3,0,1),(2:ℚ)),((4,1,0),(-2:ℚ)),((6,0,0),(1/3:ℚ)),((0,0,3),(1:ℚ)),((0,3,1),(-3:ℚ)),((1,1,2),(-9:ℚ)),((1,4,0),(3:ℚ)),((2,2,1),(18:ℚ)),((3,0,2),(6:ℚ)),((3,3,0),(-10:ℚ)),((4,1,1),(-15:ℚ)),((5,2,0),(9:ℚ)),((6,0,1),(3:ℚ)),((7,1,0),(-3:ℚ)),((9,0,0),(1/3:ℚ)),((0,0,5),(7:ℚ)),((0,3,3),(1/3:ℚ)),((0,6,1),(8:ℚ)),((1,1,4),(-67:ℚ)),((1,4,2),(39:ℚ)),((1,7,0),(-8:ℚ)),((2,2,3),(213:ℚ)),((2,5,1),(-87:ℚ)),((3,0,4),(22:ℚ)),((3,3,2),(-371:ℚ)),((3,6,0),(143/3:ℚ)),((4,1,3),(-181:ℚ)),((4,4,1),(344:ℚ)),((5,2,2),(429:ℚ)),((5,5,0),(-126:ℚ)),((6,0,3),(134/3:ℚ)),((6,3,1),(-420:ℚ)),((7,1,2),(-180:ℚ)),((7,4,0),(150:ℚ)),((8,2,1),(225:ℚ)),((9,0,2),(25:ℚ)),((9,3,0),(-275/3:ℚ)),((10,1,1),(-55:ℚ)),((11,2,0),(30:ℚ)),((12,0,1),(5:ℚ)),((13,1,0),(-5:ℚ)),((15,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,0,0),(3:ℤ)),((0,0,2),(21:ℤ)),((0,3,0),(-14:ℤ)),((1,1,1),(-84:ℤ)),((2,2,0),(63:ℤ)),((3,0,1),(42:ℤ)),((4,1,0),(-42:ℤ)),((6,0,0),(7:ℤ)),((0,0,3),(21:ℤ)),((0,3,1),(-63:ℤ)),((1,1,2),(-189:ℤ)),((1,4,0),(63:ℤ)),((2,2,1),(378:ℤ)),((3,0,2),(126:ℤ)),((3,3,0),(-210:ℤ)),((4,1,1),(-315:ℤ)),((5,2,0),(189:ℤ)),((6,0,1),(63:ℤ)),((7,1,0),(-63:ℤ)),((9,0,0),(7:ℤ)),((0,0,5),(147:ℤ)),((0,3,3),(7:ℤ)),((0,6,1),(168:ℤ)),((1,1,4),(-1407:ℤ)),((1,4,2),(819:ℤ)),((1,7,0),(-168:ℤ)),((2,2,3),(4473:ℤ)),((2,5,1),(-1827:ℤ)),((3,0,4),(462:ℤ)),((3,3,2),(-7791:ℤ)),((3,6,0),(1001:ℤ)),((4,1,3),(-3801:ℤ)),((4,4,1),(7224:ℤ)),((5,2,2),(9009:ℤ)),((5,5,0),(-2646:ℤ)),((6,0,3),(938:ℤ)),((6,3,1),(-8820:ℤ)),((7,1,2),(-3780:ℤ)),((7,4,0),(3150:ℤ)),((8,2,1),(4725:ℤ)),((9,0,2),(525:ℤ)),((9,3,0),(-1925:ℤ)),((10,1,1),(-1155:ℤ)),((11,2,0),(630:ℤ)),((12,0,1),(105:ℤ)),((13,1,0),(-105:ℤ)),((15,0,0),(7:ℤ))]
def denominator18 : ℕ := 21
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 0 6 9 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment0_6_9
