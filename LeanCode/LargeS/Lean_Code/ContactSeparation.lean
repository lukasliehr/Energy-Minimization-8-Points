import Lean_Code.ContactDirections
import Lean_Code.ContactGeometryGlobal

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def contactNeighborsWithin (Y : Fin 8 → ℝ³) (c : ℝ) (V : Finset (Fin 8)) (i : Fin 8) : Finset (Fin 8) :=
  V.filter (fun j => j ≠ i ∧ inner ℝ (Y i) (Y j) = c)

@[simp] lemma mem_contactNeighborsWithin (Y : Fin 8 → ℝ³) (c : ℝ) (V : Finset (Fin 8)) (i j : Fin 8) :
    j ∈ contactNeighborsWithin Y c V i ↔ j ∈ V ∧ j ≠ i ∧ inner ℝ (Y i) (Y j) = c := by
  simp [contactNeighborsWithin]

lemma contactNeighborsWithin_subset_erase (Y : Fin 8 → ℝ³) (c : ℝ) (V : Finset (Fin 8)) (i : Fin 8) :
    contactNeighborsWithin Y c V i ⊆ V.erase i := by
  intro j hj
  obtain ⟨hjV, hji, hij⟩ := (mem_contactNeighborsWithin Y c V i j).mp hj
  exact Finset.mem_erase.mpr ⟨hji, hjV⟩

lemma complete_four_subset_false (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (V : Finset (Fin 8)) (hV : V.card = 4)
    (hcomplete : ∀ i ∈ V, ∀ j ∈ V, i ≠ j → inner ℝ (Y i) (Y j) = c) : False := by
  apply no_four_contact_clique_of_card (ι := V) (by simpa using hV) (fun i => Y i) c
    (fun i => hY i) hc hcupper
  intro i j hij
  exact hcomplete i i.property j j.property (fun h => hij (Subtype.ext h))

lemma three_neighbors_complete_of_card_four (Y : Fin 8 → ℝ³) (c : ℝ)
    (V : Finset (Fin 8)) (hV : V.card = 4) (i : Fin 8) (hi : i ∈ V)
    (hdegree : 3 ≤ (contactNeighborsWithin Y c V i).card) :
    ∀ j ∈ V, j ≠ i → inner ℝ (Y i) (Y j) = c := by
  have hcard : (V.erase i).card ≤ (contactNeighborsWithin Y c V i).card := by
    rw [Finset.card_erase_of_mem hi, hV]
    exact hdegree
  have heq := Finset.eq_of_subset_of_card_le (contactNeighborsWithin_subset_erase Y c V i) hcard
  intro j hj hji
  have hm : j ∈ contactNeighborsWithin Y c V i := by rw [heq]; exact Finset.mem_erase.mpr ⟨hji, hj⟩
  exact ((mem_contactNeighborsWithin Y c V i j).mp hm).2.2

/-- Every nonempty closed collection of vertices with three contact
neighbors per vertex contains at least five vertices in the packing range. -/
theorem three_neighbor_component_size (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (V : Finset (Fin 8)) (hVnonempty : V.Nonempty)
    (hdegree : ∀ i ∈ V, 3 ≤ (contactNeighborsWithin Y c V i).card) : 5 ≤ V.card := by
  obtain ⟨i, hi⟩ := hVnonempty
  have hdeg := hdegree i hi
  have hle := Finset.card_le_card (contactNeighborsWithin_subset_erase Y c V i)
  rw [Finset.card_erase_of_mem hi] at hle
  by_contra h
  have hV : V.card = 4 := by omega
  apply complete_four_subset_false Y c hY hc hcupper V hV
  intro j hj k hk hjk
  exact three_neighbors_complete_of_card_four Y c V hV j hj (hdegree j hj) k hk hjk.symm

/-- A side of a possible cut vertex already needs four vertices besides
the cut vertex: a three-vertex side would force a contact `K₄`. -/
theorem contact_cut_side_size (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (A : Finset (Fin 8)) (v : Fin 8) (hA : A.Nonempty) (hv : v ∉ A)
    (hdegree : ∀ i ∈ A, 3 ≤ (contactNeighborsWithin Y c (insert v A) i).card) : 4 ≤ A.card := by
  obtain ⟨i, hi⟩ := hA
  have hiV : i ∈ insert v A := Finset.mem_insert_of_mem hi
  have hdeg := hdegree i hi
  have hle := Finset.card_le_card (contactNeighborsWithin_subset_erase Y c (insert v A) i)
  rw [Finset.card_erase_of_mem hiV, Finset.card_insert_of_notMem hv] at hle
  by_contra h
  have hAcard : A.card = 3 := by omega
  have hVcard : (insert v A).card = 4 := by rw [Finset.card_insert_of_notMem hv, hAcard]
  have hfull (j : Fin 8) (hj : j ∈ A) := three_neighbors_complete_of_card_four Y c
    (insert v A) hVcard j (Finset.mem_insert_of_mem hj) (hdegree j hj)
  apply complete_four_subset_false Y c hY hc hcupper (insert v A) hVcard
  intro j hj k hk hjk
  rcases Finset.mem_insert.mp hj with rfl | hjA
  · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left hjk.symm
    exact (real_inner_comm (Y k) (Y j)).trans (hfull k hkA j (Finset.mem_insert_self _ _) hjk)
  · exact hfull j hjA k hk hjk.symm

theorem contact_cut_partition_impossible (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (A B : Finset (Fin 8)) (v : Fin 8) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisjoint : Disjoint A B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hdegreeA : ∀ i ∈ A, 3 ≤ (contactNeighborsWithin Y c (insert v A) i).card)
    (hdegreeB : ∀ i ∈ B, 3 ≤ (contactNeighborsWithin Y c (insert v B) i).card) : False := by
  have hAc := contact_cut_side_size Y c hY hc hcupper A v hA hvA hdegreeA
  have hBc := contact_cut_side_size Y c hY hc hcupper B v hB hvB hdegreeB
  have hcard := Finset.card_le_univ (insert v (A ∪ B))
  rw [Finset.card_insert_of_notMem (by simp [hvA, hvB]), Finset.card_union_of_disjoint hdisjoint] at hcard
  norm_num at hcard
  omega

end SquareAntiprismVerification
