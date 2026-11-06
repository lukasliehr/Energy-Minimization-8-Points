import Blueprint.FiniteDefinitions
import Blueprint.RootBridge
import Blueprint.Target

/-! Exact invariant-tag ordering. Source layout:
Certificates/AnalyticFinite/analytic_layout.py:13-16 and
Certificates/SymmetricFinite/canonical.py:53-56. -/
noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

abbrev TagKey := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

def tagKey (t : Tag) : TagKey :=
  toLex (tagWeight t, toLex (t.1, toLex (t.2.1, t.2.2)))

def tagOfKey (x : TagKey) : Tag :=
  ((ofLex (ofLex x).2).1, (ofLex (ofLex (ofLex x).2).2).1,
    (ofLex (ofLex (ofLex x).2).2).2)

theorem tagOfKey_tagKey (t : Tag) : tagOfKey (tagKey t) = t := rfl

theorem tagKey_injective : Function.Injective tagKey := by
  intro t u h
  have := congrArg tagOfKey h
  simpa only [tagOfKey_tagKey] using this

def tagLE (t u : Tag) : Prop := tagKey t ≤ tagKey u

local instance : DecidableRel tagLE := fun t u =>
  inferInstanceAs (Decidable (tagKey t ≤ tagKey u))
local instance : IsTrans Tag tagLE := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
local instance : Std.Antisymm tagLE :=
  ⟨fun _ _ h₁ h₂ => tagKey_injective (le_antisymm h₁ h₂)⟩
local instance : Std.Total tagLE := ⟨fun t u => le_total (tagKey t) (tagKey u)⟩


def invariantTagList (D : ℕ) : List Tag := (InvariantTags D).sort tagLE

def retainedTagList (D : ℕ) : List Tag := (RetainedTags D).sort tagLE

def sourceInvariantTagSet (D : ℕ) : Finset Tag :=
  ((Finset.range (D+1)).product
    ((Finset.range (D/2+1)).product (Finset.range (D/3+1)))).filter
      (fun t => tagWeight t ≤ D)

def sourceInvariantTagList (D : ℕ) : List Tag := (sourceInvariantTagSet D).sort tagLE

theorem mem_InvariantTags {D : ℕ} {t : Tag} : t ∈ InvariantTags D ↔ tagWeight t ≤ D := by
  rcases t with ⟨i, j, k⟩
  simp only [InvariantTags, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, h⟩ <;> dsimp [tagWeight] at h <;> omega
#check mem_InvariantTags
#print axioms mem_InvariantTags

theorem sourceInvariantTagSet_eq (D : ℕ) : sourceInvariantTagSet D = InvariantTags D := by
  ext t
  rcases t with ⟨i, j, k⟩
  rw [mem_InvariantTags]
  simp only [sourceInvariantTagSet, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, h⟩ <;> dsimp [tagWeight] at h <;> omega
#check sourceInvariantTagSet_eq
#print axioms sourceInvariantTagSet_eq

theorem mem_invariantTagList {D : ℕ} {t : Tag} : t ∈ invariantTagList D ↔ tagWeight t ≤ D := by
  simp only [invariantTagList, Finset.mem_sort, mem_InvariantTags]
#check mem_invariantTagList
#print axioms mem_invariantTagList

theorem invariantTagList_nodup (D : ℕ) : (invariantTagList D).Nodup := by
  exact Finset.sort_nodup _ _
#check invariantTagList_nodup
#print axioms invariantTagList_nodup

theorem invariantTagList_sorted (D : ℕ) : (invariantTagList D).Pairwise (fun t u => tagKey t ≤ tagKey u) := by
  exact Finset.pairwise_sort (InvariantTags D) tagLE
#check invariantTagList_sorted
#print axioms invariantTagList_sorted

theorem mem_retainedTagList {D : ℕ} {t : Tag} : t ∈ retainedTagList D ↔ tagWeight t ≤ D ∧ t ≠ (0,0,0) ∧ t ≠ (2,0,0) := by
  simp only [retainedTagList, Finset.mem_sort, RetainedTags, Finset.mem_erase, mem_InvariantTags]
  tauto
#check mem_retainedTagList
#print axioms mem_retainedTagList

theorem retainedTagList_nodup (D : ℕ) : (retainedTagList D).Nodup := by
  exact Finset.sort_nodup _ _
#check retainedTagList_nodup
#print axioms retainedTagList_nodup

theorem sourceInvariantTagList_eq (D : ℕ) : sourceInvariantTagList D = invariantTagList D := by
  simp only [sourceInvariantTagList, invariantTagList, sourceInvariantTagSet_eq]
#check sourceInvariantTagList_eq
#print axioms sourceInvariantTagList_eq

theorem definitions_tags (D : ℕ) : (invariantTagList D).Nodup ∧ (invariantTagList D).Pairwise (fun t u => tagKey t ≤ tagKey u) ∧ (∀ t, t ∈ invariantTagList D ↔ tagWeight t ≤ D) ∧ (retainedTagList D).Nodup ∧ (∀ t, t ∈ retainedTagList D ↔ tagWeight t ≤ D ∧ t ≠ (0,0,0) ∧ t ≠ (2,0,0)) ∧ sourceInvariantTagList D = invariantTagList D := by
  exact ⟨invariantTagList_nodup D, invariantTagList_sorted D,
    fun _ => mem_invariantTagList, retainedTagList_nodup D,
    fun _ => mem_retainedTagList, sourceInvariantTagList_eq D⟩
#check definitions_tags
#print axioms definitions_tags
/-- Rank/unrank follows the actual sorted list, not an arbitrary enumeration. -/
def invariantTagEnum (D : ℕ) :
    Fin (invariantTagList D).length ≃ {t : Tag // t ∈ InvariantTags D} :=
  Equiv.ofBijective
    (fun i => ⟨(invariantTagList D).get i,
      mem_InvariantTags.mpr (mem_invariantTagList.mp (List.get_mem _ i))⟩)
    (by
      constructor
      · intro i j h
        exact (List.nodup_iff_injective_get.mp (invariantTagList_nodup D))
          (congrArg Subtype.val h)
      · intro t
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp
          (mem_invariantTagList.mpr (mem_InvariantTags.mp t.property))
        exact ⟨i, Subtype.ext hi⟩)

theorem invariantTagEnum_apply (D : ℕ) (i : Fin (invariantTagList D).length) :
    (invariantTagEnum D i).val = (invariantTagList D).get i := rfl

#print axioms invariantTagEnum
#print axioms invariantTagEnum_apply

end Blueprint.Thomson.Finite

