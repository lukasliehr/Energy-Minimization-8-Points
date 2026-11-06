import AllS.Units.N_GI.N_polar_tetrahedra.N_facet_independent
import Mathlib.Analysis.InnerProductSpace.Dual

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem normal_eq_of_independent_triple (A : Fin 3 → Point) (hA : LinearIndependent ℝ A)
    (x y : Point) (hinner : ∀i,inner ℝ x (A i)=inner ℝ y (A i)) : x=y := by
  have hspan := hA.span_eq_top_of_card_eq_finrank (by simp [Point])
  have hmap : (innerSL ℝ x).toLinearMap=(innerSL ℝ y).toLinearMap :=
    LinearMap.ext_on_range hspan hinner
  apply (innerSL_inj (𝕜:=ℝ)).mp
  ext z
  exact LinearMap.congr_fun hmap z

theorem polar_tetrahedra_matched_strict (A B : Fin 4 → Point) (c : ℝ)
    (hunit : ∀i,‖A i‖=1) (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hc : 0<c) (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    ∀i,inner ℝ (A i) (B i)<c := by
  intro i
  apply lt_of_le_of_ne (hmatched i)
  intro heq
  have hfull (k : Fin 4) : inner ℝ (A k) (B i)=c := by
    by_cases hki : k=i
    · exact hki.symm ▸ heq
    · exact hcross k i hki
  let j : Fin 4 := i+1
  have hji : j≠i := (by decide : ∀i : Fin 4,i+1≠i) i
  have hLI := polar_tetrahedra_facet_independent A B c hunit hAinj hc hcross j.succAbove Fin.succAbove_right_injective
  have hnormals : B i=B j := by
    apply normal_eq_of_independent_triple (A ∘ j.succAbove) hLI
    intro k
    change inner ℝ (B i) (A (j.succAbove k))=inner ℝ (B j) (A (j.succAbove k))
    exact (real_inner_comm _ _).trans ((hfull _).trans
      ((hcross _ _ (Fin.succAbove_ne j k)).symm.trans (real_inner_comm _ _)))
  exact hji (hBinj hnormals).symm

#print axioms normal_eq_of_independent_triple
#print axioms polar_tetrahedra_matched_strict
end Blueprint.Thomson.Tail.Implementation
