import AllS.Units.N_F.N_contact_counts

noncomputable section
namespace Blueprint.Thomson.Finite

/-- Exact geometric hypotheses for the contact classification, with actual counted neighbors. -/
structure ContactCountData (a : ℝ) (Y : Fin 8 → Point) : Prop where
  physical : physical a
  configuration : IsConfiguration Y
  counts : ∀ i, vertexContactCounts a Y i=baselineCounts

def bContactIndex : Fin 3 → Fin 4 := ![0,2,3]
def bContacts (a : ℝ) (u : Fin 3) : ℝ := contacts a (bContactIndex u)
def bpairCell (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) : Finset (Fin 8) :=
  Finset.univ.filter (fun l => l ≠ r ∧ l ≠ t ∧
    inner ℝ (Y r) (Y l)=bContacts a u ∧ inner ℝ (Y t) (Y l)=bContacts a v)
def bpairCounts (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) : ℕ :=
  (bpairCell a Y r t u v).card

theorem ContactCountData.allowed_contact {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (i j : Fin 8) (hij : i ≠ j) : inner ℝ (Y i) (Y j) ∈ Set.range (contacts a) := by
  classical
  let S := Finset.univ.biUnion (contactNeighbors a Y i)
  have hsub : S ⊆ Finset.univ.erase i := by
    intro l hl
    obtain ⟨k,_,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hl).2.1,Finset.mem_univ _⟩
  have hdis : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (contactNeighbors a Y i) := by
    intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro l hlu hlv
    have hu := (Finset.mem_filter.mp hlu).2.2
    have hv := (Finset.mem_filter.mp hlv).2.2
    exact huv (contact_injective a h.physical (hu.symm.trans hv))
  have hcard : S.card=7 := by
    rw [Finset.card_biUnion hdis]
    change (∑ k, vertexContactCounts a Y i k)=7
    rw [h.counts i]
    exact (contact_counts_baseline a).1
  have heq : S=Finset.univ.erase i := Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hj : j ∈ S := by rw [heq]; simp [Ne.symm hij]
  obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hj
  exact ⟨k,(Finset.mem_filter.mp hk).2.2.symm⟩

theorem ContactCountData.unique_B {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (i j k : Fin 8) (hij : i ≠ j) (hik : i ≠ k)
    (hj : inner ℝ (Y i) (Y j)=contacts a 1)
    (hk : inner ℝ (Y i) (Y k)=contacts a 1) : j=k := by
  have hcard : (contactNeighbors a Y i 1).card ≤ 1 := by
    have hc := congrFun (h.counts i) 1
    change (contactNeighbors a Y i 1).card=(1:ℕ) at hc
    omega
  apply (Finset.card_le_one.mp hcard) j _ k _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hij,hj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hik,hk⟩

theorem bContacts_injective (a : ℝ) (ha : physical a) : Function.Injective (bContacts a) :=
  (contact_injective a ha).comp (by decide : Function.Injective bContactIndex)

theorem bContactIndex_ne_one (u : Fin 3) : bContactIndex u ≠ 1 := by
  have h : ∀ u : Fin 3, bContactIndex u ≠ 1 := by decide
  exact h u

theorem bpair_remaining_types {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (l : Fin 8) (hlr : l ≠ r) (hlt : l ≠ t) :
    inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) ∧
    inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a) := by
  have one_side (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
      (hlr : l ≠ r) (hlt : l ≠ t) : inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) := by
    obtain ⟨k,hk⟩ := h.allowed_contact r l (Ne.symm hlr)
    have hk1 : k ≠ 1 := by
      intro he
      rw [he] at hk
      exact hlt (h.unique_B r l t (Ne.symm hlr) hrt hk.symm hB)
    have hcover : ∀ k : Fin 4, k ≠ 1 → ∃ u, bContactIndex u=k := by decide
    obtain ⟨u,hu⟩ := hcover k hk1
    exact ⟨u,by simpa only [bContacts,hu] using hk⟩
  exact ⟨one_side r t hrt hB hlr hlt,
    one_side t r (Ne.symm hrt) (by rw [real_inner_comm]; exact hB) hlt hlr⟩

theorem finite_fiber_count (S : Finset (Fin 8)) (g : Fin 8 → ℝ) (c : Fin 3 → ℝ)
    (hc : Function.Injective c) (hg : ∀ l ∈ S, g l ∈ Set.range c) :
    (∑ u, (S.filter (fun l => g l=c u)).card)=S.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ.image c) g
  rw [Finset.sum_image (by intro u _ v _ huv; exact hc huv)] at h
  have heq : S.filter (fun l => g l ∈ Finset.univ.image c)=S := by
    apply Finset.filter_eq_self.mpr
    intro l hl
    obtain ⟨u,hu⟩ := hg l hl
    exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,hu⟩
  rw [heq] at h
  exact h

theorem bpairCounts_row {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (u : Fin 3) : (∑ v, bpairCounts a Y r t u v)=2 := by
  let S := contactNeighbors a Y r (bContactIndex u)
  have hmem (l : Fin 8) (hl : l ∈ S) : l ≠ r ∧ l ≠ t := by
    obtain ⟨hlr,hprod⟩ := (Finset.mem_filter.mp hl).2
    refine ⟨hlr,?_⟩
    intro hlt
    rw [hlt,hB] at hprod
    exact bContactIndex_ne_one u ((contact_injective a h.physical hprod).symm)
  have hcell (v : Fin 3) : bpairCell a Y r t u v=
      S.filter (fun l => inner ℝ (Y t) (Y l)=bContacts a v) := by
    ext l
    constructor
    · intro hl
      obtain ⟨hlr,hlt,hu,hv⟩ := (Finset.mem_filter.mp hl).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlr,hu⟩,hv⟩
    · intro hl
      obtain ⟨hlS,hv⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hmem l hlS).1,(hmem l hlS).2,
        (Finset.mem_filter.mp hlS).2.2,hv⟩
  have hg : ∀ l ∈ S, inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a) := by
    intro l hl
    exact (bpair_remaining_types h r t hrt hB l (hmem l hl).1 (hmem l hl).2).2
  simp_rw [bpairCounts,hcell]
  rw [finite_fiber_count S _ _ (bContacts_injective a h.physical) hg]
  have hc := congrFun (h.counts r) (bContactIndex u)
  change S.card=baselineCounts (bContactIndex u) at hc
  rw [hc]
  fin_cases u <;> rfl

theorem bpairCounts_swap (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) :
    bpairCounts a Y r t u v=bpairCounts a Y t r v u := by
  unfold bpairCounts
  congr 1
  ext l
  simp [bpairCell,and_comm,and_left_comm,and_assoc]

theorem bpair_balance_contingency {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    (∀ l, l ≠ r → l ≠ t → inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) ∧
      inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a)) ∧
    (∀ u, (∑ v, bpairCounts a Y r t u v)=2) ∧
    (∀ v, (∑ u, bpairCounts a Y r t u v)=2) := by
  refine ⟨bpair_remaining_types h r t hrt hB,bpairCounts_row h r t hrt hB,?_⟩
  intro v
  simp_rw [bpairCounts_swap a Y r t]
  exact bpairCounts_row h t r (Ne.symm hrt) (by rw [real_inner_comm]; exact hB) v

theorem bpair_cell_weight_sum {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (f : ℝ → ℝ → ℝ) :
    (∑ u, ∑ v, (bpairCounts a Y r t u v:ℝ)*f (bContacts a u) (bContacts a v))=
      ∑ l : Fin 8, if l ≠ r ∧ l ≠ t then f (inner ℝ (Y r) (Y l)) (inner ℝ (Y t) (Y l)) else 0 := by
  have hn (u v : Fin 3) : (bpairCounts a Y r t u v:ℝ)*f (bContacts a u) (bContacts a v)=
      ∑ l : Fin 8, if l ≠ r ∧ l ≠ t ∧ inner ℝ (Y r) (Y l)=bContacts a u ∧
        inner ℝ (Y t) (Y l)=bContacts a v then f (bContacts a u) (bContacts a v) else 0 := by
    simp [bpairCounts,bpairCell,← Finset.sum_filter]
  simp_rw [hn]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l ≠ r ∧ l ≠ t
  · obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := bpair_remaining_types h r t hrt hB l hl.1 hl.2
    rw [← hu,← hv]
    simp [hl.1,hl.2,(bContacts_injective a h.physical).eq_iff,ite_and]
  · simp [← and_assoc,hl]

#check bpair_balance_contingency
#print axioms bpair_balance_contingency
end Blueprint.Thomson.Finite
