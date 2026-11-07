import AllS.Units.N_GI.N_polar_tetrahedra.N_coordinates

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def cubeFacet (A : Fin 4 → Point) (i : Fin 4) : Set Point :=
  convexHull ℝ (Set.range (A ∘ i.succAbove))

theorem cube_facet_plane (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c) (i : Fin 4)
    {x : Point} (hx : x∈cubeFacet A i) : inner ℝ x (B i)=c := by
  apply convexHull_min (t:={x | inner ℝ x (B i)=c}) ?_ ?_ hx
  · rintro _ ⟨j,rfl⟩
    exact hcross _ i (Fin.succAbove_ne i j)
  · intro u hu v hv a b _ _ hab
    simp only [Set.mem_setOf_eq,inner_add_left,inner_smul_left,conj_trivial] at *
    rw [hu,hv,←add_mul,hab,one_mul]

theorem cube_facet_subset_hull (A : Fin 4 → Point) (i : Fin 4) :
    cubeFacet A i ⊆ convexHull ℝ (Set.range A) :=
  convexHull_mono (by rintro _ ⟨j,rfl⟩;exact ⟨i.succAbove j,rfl⟩)

theorem cube_facet_halfspaces (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (i : Fin 4) :
    cubeFacet A i={x | inner ℝ x (B i)=c ∧ ∀j,inner ℝ x (B j)≤c} := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨cube_facet_plane A B c hcross i hx,?_⟩
    have hh := cube_facet_subset_hull A i hx
    rw [cube_convex_hull_halfspaces A B c hcross hstrict] at hh
    exact hh
  · rintro x ⟨hplane,hh⟩
    obtain ⟨w,hw,hx⟩ := cube_affine_coordinates A (cube_affine_independent A B c hcross hstrict) x
    have hnonneg : ∀j,0≤w j := fun j =>
      (cube_coordinate_halfspace A B c hcross hstrict w hw j).mp (hx ▸ hh j)
    have hi : w i=0 := (cube_coordinate_plane A B c hcross hstrict w hw i).mp (hx ▸ hplane)
    have hsum : ∑j : Fin 3,w (i.succAbove j)=1 := by
      rw [Fin.sum_univ_succAbove w i,hi,zero_add] at hw
      exact hw
    have hrepr : (∑j : Fin 3,w (i.succAbove j) • A (i.succAbove j))=x := by
      rw [Fin.sum_univ_succAbove (fun j => w j • A j) i,hi,zero_smul,zero_add] at hx
      exact hx.symm
    exact mem_convexHull_of_exists_fintype (fun j : Fin 3 => w (i.succAbove j))
      (A ∘ i.succAbove) (fun j => hnonneg _) hsum (fun j => ⟨j,rfl⟩) hrepr

theorem cube_facet_span_plane (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c) (i : Fin 4)
    {x : Point} (hx : x∈affineSpan ℝ (cubeFacet A i)) : inner ℝ x (B i)=c := by
  refine affineSpan_induction (p:=fun x => inner ℝ x (B i)=c) hx ?_ ?_
  · intro x hx; exact cube_facet_plane A B c hcross i hx
  · intro a u v w hu hv hw
    simp only [vsub_eq_sub,vadd_eq_add,inner_add_left,inner_smul_left,inner_sub_left,
      conj_trivial,hu,hv,hw,sub_self,mul_zero,zero_add]

#print axioms cube_facet_halfspaces
#print axioms cube_facet_span_plane
end Blueprint.Thomson.Tail.Implementation
