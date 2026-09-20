import Coulomb8.EnergySums
import Thomson8.EnergyInvariance

namespace Coulomb8
open Thomson8 (Index pairSum offSum_perm offSum_eq_two_pairSum)

theorem coulombEnergy_congruent (x y : Configuration) (h : Congruent x y) :
    coulombEnergy x=coulombEnergy y := by
  obtain ⟨f,σ,hσ⟩ := h
  let g : Index → Index → ℝ := fun i j => 1/‖y i-y j‖
  have hg (i j : Index) : g i j=g j i := by simp only [g,norm_sub_rev]
  have hx : coulombEnergy x=pairSum (fun i j => g (σ i) (σ j)) := by
    simp only [coulombEnergy,pairSum,Finset.sum_filter,hσ,←map_sub,f.norm_map,g]
  have hy : coulombEnergy y=pairSum g := by simp only [coulombEnergy,pairSum,Finset.sum_filter,g]
  have h := offSum_perm g σ
  rw [offSum_eq_two_pairSum _ (fun i j => hg (σ i) (σ j)),
    offSum_eq_two_pairSum g hg,←hx,←hy] at h
  linarith

#print axioms Coulomb8.coulombEnergy_congruent
end Coulomb8
