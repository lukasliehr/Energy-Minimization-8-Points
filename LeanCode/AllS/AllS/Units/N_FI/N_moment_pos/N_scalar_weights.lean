import AllS.Units.N_FI.N_geometry.N_distance_domain
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.Finite

def edgeWeightPoly : Poly3 := 1-MvPolynomial.X 0^2
def determinantWeightPoly : Poly3 :=
  1+2*MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 2-
    (MvPolynomial.X 0^2+MvPolynomial.X 1^2+MvPolynomial.X 2^2)
def gramDetScalar (u v t : ℝ) : ℝ := 1+2*u*v*t-u^2-v^2-t^2

def ScalarWeightsContract : Prop := ∀ x y z : Point,‖x‖=1 → ‖y‖=1 → ‖z‖=1 →
  0≤1-(inner ℝ x y)^2 ∧
    0≤gramDetScalar (inner ℝ x y) (inner ℝ x z) (inner ℝ y z)

theorem unit_inner_square_le_one (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    (inner ℝ x y)^2≤1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx,hy,one_mul] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0≤1+inner ℝ x y by linarith)]

theorem gramDetScalar_nonneg (x y z : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) :
    0≤gramDetScalar (inner ℝ x y) (inner ℝ x z) (inner ℝ y z) := by
  have h := (Matrix.posSemidef_gram ℝ ![x,y,z]).det_nonneg
  have he : (Matrix.gram ℝ ![x,y,z]).det=
      gramDetScalar (inner ℝ x y) (inner ℝ x z) (inner ℝ y z) := by
    simp [Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_two,
      inner_self_eq_norm_sq_to_K,hx,hy,hz,gramDetScalar,real_inner_comm]
    ring
  rwa [he] at h

theorem edgeWeightPoly_eval (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] edgeWeightPoly=1-u^2 := by simp [edgeWeightPoly]

theorem determinantWeightPoly_eval (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] determinantWeightPoly=gramDetScalar u v t := by
  simp [determinantWeightPoly,gramDetScalar]
  ring

theorem moment_pos_scalar_weights : ScalarWeightsContract := by
  intro x y z hx hy hz
  exact ⟨sub_nonneg.mpr (unit_inner_square_le_one x y hx hy),gramDetScalar_nonneg x y z hx hy hz⟩

#check moment_pos_scalar_weights
#print axioms moment_pos_scalar_weights
#check ScalarWeightsContract
#print axioms ScalarWeightsContract
end Blueprint.Thomson.Finite
