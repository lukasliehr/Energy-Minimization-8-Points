import AllS.Units.N_GI.N_components.N_closed_degree

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem components_cut_partition (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i, ‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (root : Fin 8)
    (hroot : ∃k, ContactAdj Y c root k) (v i j : Fin 8)
    (hi : i ∈ contactComponent Y c root) (hj : j ∈ contactComponent Y c root)
    (hiv : i≠v) (hjv : j≠v) (hnot : ¬ ContactReachableWithout Y c v i j) :
    ∃ A B : Finset (Fin 8), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      v∉A ∧ v∉B ∧
      (∀x∈A, 3≤(contactNeighborsWithin Y c (insert v A) x).card) ∧
      (∀x∈B, 3≤(contactNeighborsWithin Y c (insert v B) x).card) := by
  classical
  let A : Finset (Fin 8) := Finset.univ.filter (fun x =>
    x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x)
  let B : Finset (Fin 8) := Finset.univ.filter (fun x =>
    x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x)
  have hA : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hiv, .refl⟩⟩
  have hB : B.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjv, hnot⟩⟩
  have hvA : v ∉ A := by simp [A]
  have hvB : v ∉ B := by simp [B]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have ha : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x := by
      simpa [A] using hxA
    have hb : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x := by
      simpa [B] using hxB
    exact hb.2.2 ha.2.2
  refine ⟨A,B,hA,hB,hdis,hvA,hvB,?_,?_⟩
  · intro x hx
    have hxA : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x := by
      simpa [A] using hx
    apply irreducible_degree_in_closed_set Y c hY ⟨hc, by linarith⟩ hirr (insert v A) x
      (reachable_nonisolated ((mem_contactComponent Y c root x).mp hxA.1) hroot)
    intro y hxy
    by_cases hyv : y=v
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · apply Finset.mem_insert_of_mem
      have hyC := contactComponent_closed Y c root x y hxA.1 hxy
      have hyReach : ContactReachableWithout Y c v i y := hxA.2.2.tail ⟨hxy,hxA.2.1,hyv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyC,hyv,hyReach⟩
  · intro x hx
    have hxB : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x := by
      simpa [B] using hx
    apply irreducible_degree_in_closed_set Y c hY ⟨hc, by linarith⟩ hirr (insert v B) x
      (reachable_nonisolated ((mem_contactComponent Y c root x).mp hxB.1) hroot)
    intro y hxy
    by_cases hyv : y=v
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · apply Finset.mem_insert_of_mem
      have hyC := contactComponent_closed Y c root x y hxB.1 hxy
      have hyNot : ¬ ContactReachableWithout Y c v i y := by
        intro hyReach
        exact hxB.2.2 (hyReach.tail ⟨hxy.symm,hyv,hxB.2.1⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyC,hyv,hyNot⟩

end Blueprint.Thomson.Tail.Implementation
