import Coulomb8.ExtensionSemantics
import Thomson8.GramGeometry
import Thomson8.GramIsometry

namespace Coulomb8
open Thomson8 (gramResidual gram_residual_zero gram_three_det triple_gram_same gram_isometry triple_inner_ext)
open scoped InnerProductSpace

theorem contact_rigidity (x : Configuration) (hx : Admissible x)
    (hc : ∀ i j, i ≠ j → ∃ a : Fin 4, ⟪x i,x j⟫_ℝ=(nodes Coulomb8.a a)) :
    Congruent x antiprism := by
  classical
  obtain ⟨u,hu⟩ := hc 0 1 (by decide)
  obtain ⟨v,hv⟩ := hc 0 2 (by decide)
  obtain ⟨t,ht⟩ := hc 1 2 (by decide)
  have residual (i : Fin 8) :
      gramResidual (nodes Coulomb8.a u) (nodes Coulomb8.a v) (nodes Coulomb8.a t)
        ⟪x 0,x i⟫_ℝ ⟪x 1,x i⟫_ℝ ⟪x 2,x i⟫_ℝ=0 := by
    rw [←hu,←hv,←ht]
    exact gram_residual_zero _ _ _ _ (hx.1 0) (hx.1 1) (hx.1 2) (hx.1 i)
  have hb : BaseCompatible u v t := by
    obtain ⟨a,ha⟩ := hc 0 3 (by decide)
    obtain ⟨b,hb⟩ := hc 1 3 (by decide)
    obtain ⟨c,hc⟩ := hc 2 3 (by decide)
    have h := residual 3
    rw [ha,hb,hc] at h
    exact (extension_classification u v t a b c h).1
  let z := anchors u v t
  let p : Fin 3 → Point := ![antiprism z.1,antiprism z.2.1,antiprism z.2.2]
  let q : Fin 3 → Point := ![x 0,x 1,x 2]
  have hbase := base_inner u v t hb
  have hdetp : (Matrix.gram ℝ p).det ≠ 0 := by
    rw [gram_three_det _ _ _ (antiprism_unit _) (antiprism_unit _) (antiprism_unit _)]
    rw [hbase.1,hbase.2.1,hbase.2.2]
    exact contact_gramDet3_nonzero u v t
  have hdetq : (Matrix.gram ℝ q).det ≠ 0 := by
    rw [gram_three_det _ _ _ (hx.1 0) (hx.1 1) (hx.1 2),hu,hv,ht]
    exact contact_gramDet3_nonzero u v t
  have hg : ∀ i j, ⟪p i,p j⟫_ℝ=⟪q i,q j⟫_ℝ := by
    apply triple_gram_same
    · intro i; fin_cases i <;> exact (antiprism_unit _).trans (hx.1 _).symm
    · exact hbase.1.trans hu.symm
    · exact hbase.2.1.trans hv.symm
    · exact hbase.2.2.trans ht.symm
  obtain ⟨f,hf⟩ := gram_isometry p q hdetp hg
  have hpoint (i : Fin 8) : ∃ j : Fin 8, x i=f (antiprism j) := by
    by_cases hi0 : i=0
    · subst i; exact ⟨z.1,(hf 0).symm⟩
    by_cases hi1 : i=1
    · subst i; exact ⟨z.2.1,(hf 1).symm⟩
    by_cases hi2 : i=2
    · subst i; exact ⟨z.2.2,(hf 2).symm⟩
    obtain ⟨a,ha⟩ := hc 0 i (Ne.symm hi0)
    obtain ⟨b,hb⟩ := hc 1 i (Ne.symm hi1)
    obtain ⟨c,hc⟩ := hc 2 i (Ne.symm hi2)
    have hr := residual i
    rw [ha,hb,hc] at hr
    have he := extension_inner u v t a b c (extension_classification u v t a b c hr).2
    refine ⟨extensionWitness u v t a b c, ?_⟩
    apply triple_inner_ext q (Matrix.linearIndependent_of_det_gram_ne_zero hdetq)
    intro k
    rw [←hf k, f.inner_map_map, hf k]
    fin_cases k
    · exact ha.trans he.1.symm
    · exact hb.trans he.2.1.symm
    · exact hc.trans he.2.2.symm
  choose σ hσ using hpoint
  have hi : Function.Injective σ := by
    intro i j hij
    apply hx.2
    rw [hσ i,hσ j,hij]
  exact ⟨f,Equiv.ofBijective σ ((Finite.injective_iff_bijective).mp hi),hσ⟩

#print axioms contact_rigidity
end Coulomb8
