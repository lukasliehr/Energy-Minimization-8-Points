import AllS.Units.N_FI.N_quotient.N_inverse_laws

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The manuscript's retained invariant coordinates, with the two deleted
coefficients recovered by the explicit triangular compatibility equations. -/
def compatible_coordinate_quotient (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D) :
    Compatible a D ≃ₗ[ℝ] (RetainedIndex D → ℝ) :=
  LinearEquiv.ofBijective (retainCompatible a D) (by
    constructor
    · intro f g he
      rw [← (quotient_inverse_laws a ha D hD).1 f,
        ← (quotient_inverse_laws a ha D hD).1 g,he]
    · intro x
      exact ⟨recoveryCompatible a ha D hD x,(quotient_inverse_laws a ha D hD).2 x⟩)

@[simp] theorem compatible_coordinate_quotient_apply (a : ℝ) (ha : physical a)
    (D : ℕ) (hD : 2≤D) (f : Compatible a D) :
    compatible_coordinate_quotient a ha D hD f=retainCompatible a D f := rfl

theorem compatible_coordinate_quotient_symm_apply (a : ℝ) (ha : physical a)
    (D : ℕ) (hD : 2≤D) (x : RetainedIndex D → ℝ) :
    (compatible_coordinate_quotient a ha D hD).symm x=recoveryCompatible a ha D hD x := by
  apply (compatible_coordinate_quotient a ha D hD).injective
  rw [LinearEquiv.apply_symm_apply,compatible_coordinate_quotient_apply,
    (quotient_inverse_laws a ha D hD).2 x]

theorem compatible_retain_injective (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D)
    {f g : Poly3} (hf : f∈Compatible a D) (hg : g∈Compatible a D)
    (he : retainedCoordinates D ⟨f,(mem_boundedSymmetric D f).mpr
      ⟨((mem_Compatible a D f).mp hf).1,((mem_Compatible a D f).mp hf).2.1⟩⟩=
      retainedCoordinates D ⟨g,(mem_boundedSymmetric D g).mpr
      ⟨((mem_Compatible a D g).mp hg).1,((mem_Compatible a D g).mp hg).2.1⟩⟩) : f=g := by
  have h : (⟨f,hf⟩ : Compatible a D)=⟨g,hg⟩ :=
    (compatible_coordinate_quotient a ha D hD).injective he
  exact congrArg Subtype.val h

/-- The exact lexicographic source retained-row order, not an arbitrary enumeration. -/
def retainedTagEnum (D : ℕ) : Fin (retainedTagList D).length ≃ RetainedIndex D :=
  Equiv.ofBijective
    (fun i=>⟨(retainedTagList D).get i,
      mem_RetainedTags.mpr (mem_retainedTagList.mp (List.get_mem _ i))⟩)
    (by
      constructor
      · intro i j h
        exact (List.nodup_iff_injective_get.mp (retainedTagList_nodup D))
          (congrArg Subtype.val h)
      · intro t
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp
          (mem_retainedTagList.mpr (mem_RetainedTags.mp t.property))
        exact ⟨i,Subtype.ext hi⟩)

@[simp] theorem retainedTagEnum_apply (D : ℕ) (i : Fin (retainedTagList D).length) :
    (retainedTagEnum D i).val=(retainedTagList D).get i := rfl

def retainedSourceCoordinates (D : ℕ) (f : boundedSymmetric D)
    (i : Fin (retainedTagList D).length) : ℝ := retainedCoordinates D f (retainedTagEnum D i)

theorem retainedSourceCoordinates_injective (a : ℝ) (ha : physical a)
    (D : ℕ) (hD : 2≤D) {f g : Compatible a D}
    (he : retainedSourceCoordinates D (compatibleToBounded a D f)=
      retainedSourceCoordinates D (compatibleToBounded a D g)) : f=g := by
  apply (compatible_coordinate_quotient a ha D hD).injective
  funext t
  obtain ⟨i,rfl⟩ := (retainedTagEnum D).surjective t
  exact congrFun he i

#check compatible_coordinate_quotient
#print axioms compatible_coordinate_quotient
#check compatible_coordinate_quotient_symm_apply
#print axioms compatible_coordinate_quotient_symm_apply
end Blueprint.Thomson.Finite
