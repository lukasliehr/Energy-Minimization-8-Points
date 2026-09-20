import Coulomb8.GlobalMinimum
import Thomson8.EqualityContacts

namespace Coulomb8
open scoped InnerProductSpace
open Thomson8 (Index pairSum pairSum_zero_elim inner_unit_bounds admissible_inner_lt_one unit_antipodal third_index)

theorem equality_hermite_energy (x : Configuration) (hx : Admissible x)
    (he : coulombEnergy x=optimalEnergy) : hermiteEnergy x=optimalEnergy :=
  le_antisymm (he ▸ hermiteEnergy_le_coulombEnergy x hx) (certificate_lower_bound x hx.1)

theorem equality_pair_gap (x : Configuration) (hx : Admissible x)
    (he : coulombEnergy x=optimalEnergy) (i j : Index) (hij : i ≠ j) :
    phi ⟪x i,x j⟫_ℝ-H ⟪x i,x j⟫_ℝ=0 := by
  have hnn (i j : Index) (hij : i<j) : 0 ≤ phi ⟪x i,x j⟫_ℝ-H ⟪x i,x j⟫_ℝ :=
    sub_nonneg.mpr (minorant ⟨(inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
      admissible_inner_lt_one x hx i j hij.ne⟩)
  have hsum : pairSum (fun i j => phi ⟪x i,x j⟫_ℝ-H ⟪x i,x j⟫_ℝ)=0 := by
    have hsplit : pairSum (fun i j => phi ⟪x i,x j⟫_ℝ-H ⟪x i,x j⟫_ℝ)=
        coulombEnergy x-hermiteEnergy x := by
      rw [coulombEnergy_eq_pairs x hx.1]
      simp only [pairSum,hermiteEnergy,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    rw [hsplit,he,equality_hermite_energy x hx he,sub_self]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact pairSum_zero_elim _ hnn hsum i j hlt
  · have h := pairSum_zero_elim _ hnn hsum j i hgt
    simpa only [real_inner_comm] using h

theorem equality_contact_or_antipodal (x : Configuration) (hx : Admissible x)
    (he : coulombEnergy x=optimalEnergy) (i j : Index) (hij : i ≠ j) :
    ⟪x i,x j⟫_ℝ = -1 ∨ ∃ k : Fin 4, ⟪x i,x j⟫_ℝ=nodes a k :=
  (minorant_equality ⟨(inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
    admissible_inner_lt_one x hx i j hij⟩).mp
    (sub_eq_zero.mp (equality_pair_gap x hx he i j hij)).symm

theorem equality_no_antipodes (x : Configuration) (hx : Admissible x)
    (he : coulombEnergy x=optimalEnergy) (i j : Index) (hij : i ≠ j) : ⟪x i,x j⟫_ℝ ≠ -1 := by
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
  obtain ⟨u,hu⟩ := (equality_contact_or_antipodal x hx he i k hki.symm).resolve_left hik
  obtain ⟨v,hv⟩ := (equality_contact_or_antipodal x hx he j k hkj.symm).resolve_left hjk
  apply nodes_no_opposites u v
  rw [←hu,←hv,hanti,inner_neg_left]
  ring

theorem equality_contacts (x : Configuration) (hx : Admissible x)
    (he : coulombEnergy x=optimalEnergy) (i j : Index) (hij : i ≠ j) :
    ∃ k : Fin 4, ⟪x i,x j⟫_ℝ=nodes a k :=
  (equality_contact_or_antipodal x hx he i j hij).resolve_left (equality_no_antipodes x hx he i j hij)

end Coulomb8

#print axioms Coulomb8.equality_contacts
