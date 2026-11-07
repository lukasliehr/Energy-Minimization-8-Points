import AllS.Units.N_F.N_quotient

noncomputable section
namespace Blueprint.CAP
open Blueprint.Thomson.Finite
local instance : DecidableRel tagLE := fun t u => inferInstanceAs (Decidable (tagKey t≤tagKey u))
local instance : IsTrans Tag tagLE := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
local instance : Std.Antisymm tagLE := ⟨fun _ _ h₁ h₂ => tagKey_injective (le_antisymm h₁ h₂)⟩
local instance : Std.Total tagLE := ⟨fun t u => le_total (tagKey t) (tagKey u)⟩

theorem fixedRetainedList_literal (D : ℕ) (l : List Tag) (hn : l.Nodup)
    (he : l.toFinset=RetainedTags D) (hs : l.Pairwise (fun t u => tagKey t≤tagKey u)) :
    retainedTagList D=l := by
  unfold retainedTagList
  rw [← he]
  exact (List.toFinset_sort (r:=tagLE) hn).2 hs

#print axioms fixedRetainedList_literal
end Blueprint.CAP
