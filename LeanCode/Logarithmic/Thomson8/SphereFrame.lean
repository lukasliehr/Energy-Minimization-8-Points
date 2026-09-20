import Thomson8.GeometryBasics
import Thomson8.Kernels

namespace Thomson8

open scoped InnerProductSpace

theorem unit_frame (x : Point) (hx : ‖x‖=1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Point, b 0=x := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => x)) := by
    constructor
    · intro i; exact hx
    · intro i j hij
      exfalso
      apply hij
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans (Set.mem_singleton_iff.mp j.property).symm
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [Point])
  exact ⟨b,hb 0 (by simp)⟩

noncomputable def tangentComplex (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) : ℂ :=
  ⟨⟪b 1,y⟫_ℝ,⟪b 2,y⟫_ℝ⟩

theorem inner_frame (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    ⟪y,z⟫_ℝ = ⟪b 0,y⟫_ℝ*⟪b 0,z⟫_ℝ +
      ⟪b 1,y⟫_ℝ*⟪b 1,z⟫_ℝ + ⟪b 2,y⟫_ℝ*⟪b 2,z⟫_ℝ := by
  have h := b.sum_inner_mul_inner y z
  simpa [Fin.sum_univ_succ,real_inner_comm,add_assoc] using h.symm

theorem tangent_re (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    (tangentComplex b y * star (tangentComplex b z)).re =
      ⟪y,z⟫_ℝ - ⟪b 0,y⟫_ℝ*⟪b 0,z⟫_ℝ := by
  rw [inner_frame b y z]
  simp [tangentComplex,Complex.mul_re,Complex.star_def]
  ring

theorem tangent_normSq (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) (hy : ‖y‖=1) :
    Complex.normSq (tangentComplex b y) = 1-⟪b 0,y⟫_ℝ^2 := by
  have h := inner_frame b y y
  rw [real_inner_self_eq_norm_sq,hy] at h
  simp [tangentComplex,Complex.normSq_apply]
  nlinarith

theorem spherical_kernel_features (b : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (k : ℕ) :
    kernelQ k ⟪b 0,y⟫_ℝ ⟪b 0,z⟫_ℝ ⟪y,z⟫_ℝ =
      ((tangentComplex b y)^k).re*((tangentComplex b z)^k).re +
      ((tangentComplex b y)^k).im*((tangentComplex b z)^k).im := by
  rw [kernelQ_complex k _ _ _ (tangentComplex b y * star (tangentComplex b z))
    (tangent_re b y z)]
  · exact complex_power_gram _ _ _
  · simp [Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,tangent_normSq b y hy,
      tangent_normSq b z hz]

#print axioms unit_frame
#print axioms spherical_kernel_features

end Thomson8
