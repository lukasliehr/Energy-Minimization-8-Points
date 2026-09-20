import Thomson8.GeometryBasics
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Thomson8
open Module
open scoped InnerProductSpace

noncomputable def tripleBasis (v : Fin 3 → Point) (hv : LinearIndependent ℝ v) :
    Basis (Fin 3) ℝ Point :=
  basisOfLinearIndependentOfCardEqFinrank hv (by simp [Point])

@[simp] theorem tripleBasis_apply (v : Fin 3 → Point) (hv : LinearIndependent ℝ v) (i : Fin 3) :
    tripleBasis v hv i = v i := by simp [tripleBasis]

theorem triple_inner_ext (v : Fin 3 → Point) (hv : LinearIndependent ℝ v) (x y : Point)
    (h : ∀ i, ⟪v i,x⟫_ℝ=⟪v i,y⟫_ℝ) : x=y := by
  apply ext_inner_left ℝ
  intro z
  rw [← (tripleBasis v hv).sum_repr z]
  simp only [sum_inner, real_inner_smul_left, tripleBasis_apply, h]

theorem triple_gram_same (v w : Fin 3 → Point) (hn : ∀ i, ‖v i‖=‖w i‖)
    (h01 : ⟪v 0,v 1⟫_ℝ=⟪w 0,w 1⟫_ℝ)
    (h02 : ⟪v 0,v 2⟫_ℝ=⟪w 0,w 2⟫_ℝ)
    (h12 : ⟪v 1,v 2⟫_ℝ=⟪w 1,w 2⟫_ℝ) :
    ∀ i j, ⟪v i,v j⟫_ℝ=⟪w i,w j⟫_ℝ := by
  intro i j
  fin_cases i <;> fin_cases j
  · change ⟪v 0,v 0⟫_ℝ=⟪w 0,w 0⟫_ℝ
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hn]
  · exact h01
  · exact h02
  · change ⟪v 1,v 0⟫_ℝ=⟪w 1,w 0⟫_ℝ
    rw [real_inner_comm (v 0) (v 1),real_inner_comm (w 0) (w 1)]
    exact h01
  · change ⟪v 1,v 1⟫_ℝ=⟪w 1,w 1⟫_ℝ
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hn]
  · exact h12
  · change ⟪v 2,v 0⟫_ℝ=⟪w 2,w 0⟫_ℝ
    rw [real_inner_comm (v 0) (v 2),real_inner_comm (w 0) (w 2)]
    exact h02
  · change ⟪v 2,v 1⟫_ℝ=⟪w 2,w 1⟫_ℝ
    rw [real_inner_comm (v 1) (v 2),real_inner_comm (w 1) (w 2)]
    exact h12
  · change ⟪v 2,v 2⟫_ℝ=⟪w 2,w 2⟫_ℝ
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hn]

theorem gram_isometry (v w : Fin 3 → Point) (hv : (Matrix.gram ℝ v).det ≠ 0)
    (hg : ∀ i j, ⟪v i,v j⟫_ℝ=⟪w i,w j⟫_ℝ) :
    ∃ f : Point ≃ₗᵢ[ℝ] Point, ∀ i, f (v i)=w i := by
  have hw : (Matrix.gram ℝ w).det ≠ 0 := by
    have he : Matrix.gram ℝ v=Matrix.gram ℝ w := by ext i j; exact hg i j
    rwa [← he]
  let b := tripleBasis v (Matrix.linearIndependent_of_det_gram_ne_zero hv)
  let c := tripleBasis w (Matrix.linearIndependent_of_det_gram_ne_zero hw)
  let e := b.equiv c (Equiv.refl (Fin 3))
  have hb (i : Fin 3) : b i=v i := tripleBasis_apply _ _ i
  have hc (i : Fin 3) : c i=w i := tripleBasis_apply _ _ i
  have he (i : Fin 3) : e (v i)=w i := by
    have he' : e (b i)=c i := by
      exact Module.Basis.equiv_apply (b := b) (b' := c) (e := Equiv.refl (Fin 3)) i
    simpa only [hb,hc] using he' 
  have hi (x y : Point) : ⟪e x,e y⟫_ℝ=⟪x,y⟫_ℝ := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [hb,he,hg]
  exact ⟨e.isometryOfInner hi, he⟩

#print axioms gram_isometry
end Thomson8
