import AllS.Units.N_FI.N_counting.N_pair_identity

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def pairPotential (s : ℝ) (Y : Configuration) (i j : Fin 8) : ℝ :=
  if s=0 then -Real.log ‖Y i-Y j‖ else ‖Y i-Y j‖^(-s)

theorem pairPotential_symmetric (s : ℝ) (Y : Configuration) (i j : Fin 8) :
    pairPotential s Y i j=pairPotential s Y j i := by
  simp only [pairPotential,norm_sub_rev]

theorem offSum_permutation (f : Fin 8 → Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) :
    GenericMoments.offSum (fun i j => f (σ i) (σ j))=GenericMoments.offSum f := by
  unfold GenericMoments.offSum
  have he (i j : Fin 8) : (if i≠j then f (σ i) (σ j) else 0)=
      if σ i≠σ j then f (σ i) (σ j) else 0 := by simp only [σ.injective.ne_iff]
  simp_rw [he]
  trans ∑ i : Fin 8,∑ j : Fin 8,if σ i≠j then f (σ i) j else 0
  · apply Finset.sum_congr rfl
    intro i hi
    exact Equiv.sum_comp σ (fun j => if σ i≠j then f (σ i) j else 0)
  · exact Equiv.sum_comp σ (fun i => ∑ j : Fin 8,if i≠j then f i j else 0)

theorem cell_soundness_congruence_energy (s : ℝ) (Y Z : Configuration)
    (h : Congruent Y Z) : E s Y=E s Z := by
  obtain ⟨U,σ,h⟩ := h
  have hp (i j : Fin 8) : pairPotential s Y i j=pairPotential s Z (σ i) (σ j) := by
    have hn : ‖Y i-Y j‖=‖Z (σ i)-Z (σ j)‖ := by
      rw [h i,h j,← U.map_sub,U.norm_map]
    simp only [pairPotential,hn]
  have ho : GenericMoments.offSum (pairPotential s Y)=GenericMoments.offSum (pairPotential s Z) := by
    simp_rw [show pairPotential s Y=(fun i j => pairPotential s Z (σ i) (σ j)) from funext fun i => funext (hp i)]
    exact offSum_permutation _ σ
  rw [offSum_eq_twoPairSum _ (pairPotential_symmetric s Y),
    offSum_eq_twoPairSum _ (pairPotential_symmetric s Z)] at ho
  change PairSum (pairPotential s Y)=PairSum (pairPotential s Z)
  linarith

#check cell_soundness_congruence_energy
#print axioms cell_soundness_congruence_energy
end Blueprint.Thomson.Finite
