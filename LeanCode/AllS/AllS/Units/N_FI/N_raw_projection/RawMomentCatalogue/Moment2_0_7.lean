import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_7
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def entry : RawCatalogue.SparsePoly := [((0,2,1),(-35/3:ℚ)),((1,0,2),(-35/3:ℚ)),((1,3,0),(35/3:ℚ)),((2,1,1),(35:ℚ)),((3,2,0),(-70/3:ℚ)),((4,0,1),(-35/3:ℚ)),((5,1,0),(35/3:ℚ)),((7,0,0),(-5/3:ℚ)),((0,0,3),(-5:ℚ)),((0,3,1),(-27:ℚ)),((1,1,2),(3:ℚ)),((1,4,0),(27:ℚ)),((2,2,1),(57:ℚ)),((3,0,2),(-9:ℚ)),((3,3,0),(-55:ℚ)),((4,1,1),(-30:ℚ)),((5,2,0),(39:ℚ)),((6,0,1),(6:ℚ)),((7,1,0),(-12:ℚ)),((9,0,0),(4/3:ℚ)),((0,2,2),(-56:ℚ)),((1,0,3),(-56:ℚ)),((1,3,1),(56:ℚ)),((2,1,2),(168:ℚ)),((3,2,1),(-112:ℚ)),((4,0,2),(-56:ℚ)),((5,1,1),(56:ℚ)),((7,0,1),(-8:ℚ)),((0,1,3),(4/3:ℚ)),((0,4,1),(32/3:ℚ)),((1,2,2),(10:ℚ)),((1,5,0),(-32/3:ℚ)),((2,0,3),(-35/3:ℚ)),((2,3,1),(-131/3:ℚ)),((3,1,2),(31/3:ℚ)),((3,4,0),(97/3:ℚ)),((4,2,1),(34:ℚ)),((5,0,2),(-4:ℚ)),((5,3,0),(-98/3:ℚ)),((6,1,1),(-35/3:ℚ)),((7,2,0),(47/3:ℚ)),((8,0,1),(5/3:ℚ)),((9,1,0),(-11/3:ℚ)),((11,0,0),(1/3:ℚ))]
def raw18 : List (Tag × ℤ) := [((0,2,1),(-35:ℤ)),((1,0,2),(-35:ℤ)),((1,3,0),(35:ℤ)),((2,1,1),(105:ℤ)),((3,2,0),(-70:ℤ)),((4,0,1),(-35:ℤ)),((5,1,0),(35:ℤ)),((7,0,0),(-5:ℤ)),((0,0,3),(-15:ℤ)),((0,3,1),(-81:ℤ)),((1,1,2),(9:ℤ)),((1,4,0),(81:ℤ)),((2,2,1),(171:ℤ)),((3,0,2),(-27:ℤ)),((3,3,0),(-165:ℤ)),((4,1,1),(-90:ℤ)),((5,2,0),(117:ℤ)),((6,0,1),(18:ℤ)),((7,1,0),(-36:ℤ)),((9,0,0),(4:ℤ)),((0,2,2),(-168:ℤ)),((1,0,3),(-168:ℤ)),((1,3,1),(168:ℤ)),((2,1,2),(504:ℤ)),((3,2,1),(-336:ℤ)),((4,0,2),(-168:ℤ)),((5,1,1),(168:ℤ)),((7,0,1),(-24:ℤ)),((0,1,3),(4:ℤ)),((0,4,1),(32:ℤ)),((1,2,2),(30:ℤ)),((1,5,0),(-32:ℤ)),((2,0,3),(-35:ℤ)),((2,3,1),(-131:ℤ)),((3,1,2),(31:ℤ)),((3,4,0),(97:ℤ)),((4,2,1),(102:ℤ)),((5,0,2),(-12:ℤ)),((5,3,0),(-98:ℤ)),((6,1,1),(-35:ℤ)),((7,2,0),(47:ℤ)),((8,0,1),(5:ℤ)),((9,1,0),(-11:ℤ)),((11,0,0),(1:ℤ))]
def denominator18 : ℕ := 3
theorem normalize_18 : raw18.map (fun x => (x.1, (x.2:ℚ)/denominator18))=entry := by norm_num [raw18,denominator18,entry]
theorem denominator_18_positive : 0<denominator18 := by decide
theorem identity : sparseInvariantPolynomial entry=kernelRPoly 2 0 7 := by
  simp only [kernelRPoly,kernelSPoly,reynolds_six]
  apply MvPolynomial.funext
  intro x
  norm_num [entry,sparseInvariantPolynomial_cons,sparseInvariantPolynomial_nil,
    invariantMonomial,sigma,e2,e3,kernelQPoly,
    Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff,Algebra.smul_def,Matrix.cons_val_two]
  all_goals norm_num only [map_ofNat,map_natCast]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawMomentCatalogue.Moment2_0_7
