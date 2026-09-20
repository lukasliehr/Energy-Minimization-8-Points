import Thomson8.ExtensionChecks

namespace Thomson8
open scoped InnerProductSpace

theorem candidateValue_contact (c : Fin 5) (a : Fin 4) (h : c.val=a.val+1) :
    candidateValue c=(contactK a).eval := by
  fin_cases c <;> fin_cases a <;> norm_num at h <;> rfl

theorem base_inner (u v t : Fin 4) (h : BaseCompatible u v t) :
    let z := anchors u v t
    ⟪antiprism z.1,antiprism z.2.1⟫_ℝ=(contactK u).eval ∧
    ⟪antiprism z.1,antiprism z.2.2⟫_ℝ=(contactK v).eval ∧
    ⟪antiprism z.2.1,antiprism z.2.2⟫_ℝ=(contactK t).eval := by
  rcases h with ⟨_,_,_,h1,h2,h3⟩
  exact ⟨(antiprism_inner _ _).trans (candidateValue_contact _ _ h1),
    (antiprism_inner _ _).trans (candidateValue_contact _ _ h2),
    (antiprism_inner _ _).trans (candidateValue_contact _ _ h3)⟩

theorem extension_inner (u v t a b c : Fin 4) (h : ExtensionCompatible u v t a b c) :
    let z := anchors u v t
    let w := extensionWitness u v t a b c
    ⟪antiprism z.1,antiprism w⟫_ℝ=(contactK a).eval ∧
    ⟪antiprism z.2.1,antiprism w⟫_ℝ=(contactK b).eval ∧
    ⟪antiprism z.2.2,antiprism w⟫_ℝ=(contactK c).eval := by
  rcases h with ⟨_,_,_,h1,h2,h3⟩
  exact ⟨(antiprism_inner _ _).trans (candidateValue_contact _ _ h1),
    (antiprism_inner _ _).trans (candidateValue_contact _ _ h2),
    (antiprism_inner _ _).trans (candidateValue_contact _ _ h3)⟩

theorem extension_classification (u v t a b c : Fin 4)
    (hr : gramResidual (contactK u).eval (contactK v).eval (contactK t).eval
      (contactK a).eval (contactK b).eval (contactK c).eval=0) :
    BaseCompatible u v t ∧ ExtensionCompatible u v t a b c :=
  extensionCheck_sound u v t a b c (all_extension_checks u v t a b c) hr

#print axioms extension_classification
end Thomson8
