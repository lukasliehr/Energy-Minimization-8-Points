import Thomson8.EnergySums

namespace Thomson8

theorem offSum_perm (g : Index → Index → ℝ) (σ : Equiv.Perm Index) :
    offSum (fun i j => g (σ i) (σ j))=offSum g := by
  unfold offSum
  have hn : (fun i j : Index => if i ≠ j then g (σ i) (σ j) else 0) =
      (fun i j : Index => if σ i ≠ σ j then g (σ i) (σ j) else 0) := by
    funext i j
    simp only [σ.injective.ne_iff]
  change (∑ i : Index, ∑ j : Index, (fun i j => if i ≠ j then g (σ i) (σ j) else 0) i j)=_
  rw [hn]
  have h (i : Index) : (∑ j : Index, if σ i ≠ σ j then g (σ i) (σ j) else 0)=
      ∑ j : Index, if σ i ≠ j then g (σ i) j else 0 :=
    Equiv.sum_comp σ (fun j => if σ i ≠ j then g (σ i) j else 0)
  simp only [h]
  exact Equiv.sum_comp σ (fun i => ∑ j : Index, if i ≠ j then g i j else 0)

theorem logEnergy_congruent (x y : Configuration) (h : Congruent x y) :
    logEnergy x=logEnergy y := by
  obtain ⟨f,σ,hσ⟩ := h
  let g : Index → Index → ℝ := fun i j => -Real.log ‖y i-y j‖
  have hg (i j : Index) : g i j=g j i := by simp only [g,norm_sub_rev]
  have hx : logEnergy x=pairSum (fun i j => g (σ i) (σ j)) := by
    simp only [logEnergy,pairSum,Finset.sum_filter,hσ,←map_sub,f.norm_map,g]
  have hy : logEnergy y=pairSum g := by simp only [logEnergy,pairSum,Finset.sum_filter,g]
  have h := offSum_perm g σ
  rw [offSum_eq_two_pairSum _ (fun i j => hg (σ i) (σ j)),
    offSum_eq_two_pairSum g hg,←hx,←hy] at h
  linarith

#print axioms logEnergy_congruent
end Thomson8
