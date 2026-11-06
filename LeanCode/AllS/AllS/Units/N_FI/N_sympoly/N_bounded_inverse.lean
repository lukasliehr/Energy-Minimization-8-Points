import AllS.Units.N_FI.N_sympoly.N_component_commutation
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
namespace Blueprint.Thomson.Finite

theorem sympoly_bounded_inverse (p : Poly3) (D : ℕ)
    (hs : p.IsSymmetric) (hd : p.totalDegree ≤ D) :
  ∃! q : Poly3, invariantSubst q = p ∧
    ∀ d ∈ q.support, Finsupp.weight invariantWeight d ≤ D := by
  obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgHom_fin_bijective ℝ 3).surjective ⟨p, hs⟩
  have hS : invariantSubst q = p :=
    (sympoly_elementary_bridge q).trans (congrArg Subtype.val hq)
  have hW : ∀ d ∈ q.support, Finsupp.weight invariantWeight d ≤ D := by
    intro d hdq
    by_contra h
    have hn : D < Finsupp.weight invariantWeight d := lt_of_not_ge h
    have hc : MvPolynomial.weightedHomogeneousComponent invariantWeight
        (Finsupp.weight invariantWeight d) q = 0 := by
      apply invariantSubst_injective
      rw [sympoly_component_commutation, hS, map_zero]
      exact MvPolynomial.homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt hd hn)
    have hcoeff := congrArg (MvPolynomial.coeff d) hc
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl,
      MvPolynomial.coeff_zero] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hdq) hcoeff
  refine ⟨q, ⟨hS, hW⟩, ?_⟩
  intro r hr
  exact invariantSubst_injective (hr.1.trans hS.symm)

#check sympoly_bounded_inverse
#print axioms sympoly_bounded_inverse
end Blueprint.Thomson.Finite
