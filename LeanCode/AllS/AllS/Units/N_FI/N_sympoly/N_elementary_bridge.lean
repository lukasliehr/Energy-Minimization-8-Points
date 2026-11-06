import AllS.Units.N_F.N_definitions
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def invariantSubst : Poly3 →ₐ[ℝ] Poly3 :=
  MvPolynomial.aeval (fun i : Fin 3 => ![sigma, e2, e3] i)

def invariantWeight (i : Fin 3) : ℕ := i.val + 1

theorem esymm_fin_three (i : Fin 3) : MvPolynomial.esymm (Fin 3) ℝ (i.val + 1) = ![sigma, e2, e3] i := by
  fin_cases i
  · simp [MvPolynomial.esymm_one, Fin.sum_univ_succ, sigma, add_assoc]
  · have hs : Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) =
        {{0, 1}, {0, 2}, {1, 2}} := by decide
    have h₁ : ({0, 1} : Finset (Fin 3)) ∉
        ({{0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide
    have h₂ : ({0, 2} : Finset (Fin 3)) ∉
        ({{1, 2}} : Finset (Finset (Fin 3))) := by decide
    change (∑ t ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)),
      ∏ j ∈ t, (MvPolynomial.X j : Poly3)) = e2
    rw [hs, Finset.sum_insert h₁, Finset.sum_insert h₂, Finset.sum_singleton]
    simp [e2, add_assoc]
  · have hs : Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) =
        {Finset.univ} := by decide
    simp [MvPolynomial.esymm, hs, Fin.prod_univ_succ, e3, mul_assoc]
#check esymm_fin_three
#print axioms esymm_fin_three

theorem sympoly_elementary_bridge (p : Poly3) : invariantSubst p = (MvPolynomial.esymmAlgHom (Fin 3) ℝ 3 p).val := by
  rw [MvPolynomial.esymmAlgHom_apply]
  have h : (fun i : Fin 3 => MvPolynomial.esymm (Fin 3) ℝ (i.val + 1)) =
      fun i : Fin 3 => ![sigma, e2, e3] i := funext esymm_fin_three
  rw [h]
  rfl
#check sympoly_elementary_bridge
#print axioms sympoly_elementary_bridge

theorem invariantSubst_injective  : Function.Injective invariantSubst := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective ℝ (n := 3) (m := 3) le_rfl
  apply Subtype.ext
  exact (sympoly_elementary_bridge p).symm.trans (h.trans (sympoly_elementary_bridge q))
#check invariantSubst_injective
#print axioms invariantSubst_injective

theorem invariantSubst_symmetric (p : Poly3) : (invariantSubst p).IsSymmetric := by
  rw [sympoly_elementary_bridge]
  exact (MvPolynomial.esymmAlgHom (Fin 3) ℝ 3 p).property
#check invariantSubst_symmetric
#print axioms invariantSubst_symmetric
end Blueprint.Thomson.Finite
