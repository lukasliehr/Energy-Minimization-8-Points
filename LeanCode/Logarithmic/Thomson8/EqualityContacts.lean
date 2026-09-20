import Thomson8.GlobalMinimum
import Thomson8.NoOpposites

namespace Thomson8

open scoped InnerProductSpace

theorem pairSum_zero_elim (f : Index → Index → ℝ) (hf : ∀ i j, i < j → 0≤f i j)
    (hs : pairSum f=0) (i j : Index) (hij : i < j) : f i j=0 := by
  have hp (a b : Index) : 0 ≤ if a < b then f a b else 0 := by
    split_ifs with hab
    · exact hf a b hab
    · exact le_rfl
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun b _ => hp a b)).mp hs i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hp i b)).mp hi j (Finset.mem_univ j)
  simpa [hij] using hj

theorem equality_hermite_energy (x : Configuration) (hx : Admissible x)
    (he : logEnergy x=optimalEnergy) : hermiteEnergy x=optimalEnergy :=
  le_antisymm (he ▸ hermiteEnergy_le_logEnergy x hx) (certificate_lower_bound x hx.1)

theorem equality_pair_gap (x : Configuration) (hx : Admissible x)
    (he : logEnergy x=optimalEnergy) (i j : Index) (hij : i≠j) :
    minorantGap ⟪x i,x j⟫_ℝ=0 := by
  have hnn (i j : Index) (hij : i < j) : 0 ≤ minorantGap ⟪x i,x j⟫_ℝ :=
    sub_nonneg.mpr (H_minorant ⟨(inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
      admissible_inner_lt_one x hx i j hij.ne⟩)
  have hsum : pairSum (fun i j => minorantGap ⟪x i,x j⟫_ℝ)=0 := by
    have hsplit : pairSum (fun i j => minorantGap ⟪x i,x j⟫_ℝ) =
        logEnergy x-hermiteEnergy x := by
      rw [logEnergy_eq_pairs x hx.1]
      simp only [pairSum,hermiteEnergy,minorantGap,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [hsplit,he,equality_hermite_energy x hx he,sub_self]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact pairSum_zero_elim _ hnn hsum i j hlt
  · have h := pairSum_zero_elim _ hnn hsum j i hgt
    simpa only [real_inner_comm] using h

theorem equality_contact_or_antipodal (x : Configuration) (hx : Admissible x)
    (he : logEnergy x=optimalEnergy) (i j : Index) (hij : i≠j) :
    ⟪x i,x j⟫_ℝ = -1 ∨ ∃ a : Fin 4, ⟪x i,x j⟫_ℝ=(nodes.getD a K.zero).eval := by
  have h := (H_minorant_equality ⟨(inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
    admissible_inner_lt_one x hx i j hij⟩).mp
    (sub_eq_zero.mp (equality_pair_gap x hx he i j hij)).symm
  rcases h with hm | hA | hB | hC | hD
  · exact Or.inl hm
  · exact Or.inr ⟨⟨0,by decide⟩,by simpa [nodes] using hA⟩
  · exact Or.inr ⟨⟨1,by decide⟩,by simpa [nodes] using hB⟩
  · exact Or.inr ⟨⟨2,by decide⟩,by simpa [nodes] using hC⟩
  · exact Or.inr ⟨⟨3,by decide⟩,by simpa [nodes] using hD⟩

theorem equality_no_antipodes (x : Configuration) (hx : Admissible x)
    (he : logEnergy x=optimalEnergy) (i j : Index) (hij : i≠j) : ⟪x i,x j⟫_ℝ ≠ -1 := by
  intro ha
  have hanti := unit_antipodal (x i) (x j) (hx.1 i) (hx.1 j) ha
  obtain ⟨k,hki,hkj⟩ := third_index i j
  have hik : ⟪x i,x k⟫_ℝ ≠ -1 := by
    intro h
    have hk := unit_antipodal (x i) (x k) (hx.1 i) (hx.1 k) h
    exact hkj (hx.2 (hk.trans hanti.symm))
  have hjk : ⟪x j,x k⟫_ℝ ≠ -1 := by
    intro h
    have hk := unit_antipodal (x j) (x k) (hx.1 j) (hx.1 k) h
    rw [hanti,neg_neg] at hk
    exact hki (hx.2 hk)
  obtain ⟨a,ha⟩ := (equality_contact_or_antipodal x hx he i k hki.symm).resolve_left hik
  obtain ⟨b,hb⟩ := (equality_contact_or_antipodal x hx he j k hkj.symm).resolve_left hjk
  apply nodes_no_opposites a b
  rw [←ha,←hb,hanti,inner_neg_left]
  ring

theorem equality_contacts (x : Configuration) (hx : Admissible x)
    (he : logEnergy x=optimalEnergy) (i j : Index) (hij : i≠j) :
    ∃ a : Fin 4, ⟪x i,x j⟫_ℝ=(nodes.getD a K.zero).eval :=
  (equality_contact_or_antipodal x hx he i j hij).resolve_left (equality_no_antipodes x hx he i j hij)

#print axioms equality_contacts

end Thomson8
