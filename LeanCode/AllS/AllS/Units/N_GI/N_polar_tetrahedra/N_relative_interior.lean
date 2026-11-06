import AllS.Units.N_GI.N_polar_tetrahedra.N_facet_hull

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_origin_interior (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) :
    (0 : Point)∈interior (convexHull ℝ (Set.range A)) := by
  rw [cube_convex_hull_halfspaces A B c hcross hstrict]
  apply mem_interior.mpr
  refine ⟨⋂i : Fin 4,{x : Point | inner ℝ x (B i)<c},?_,?_,?_⟩
  · intro x hx i
    exact (Set.mem_iInter.mp hx i).le
  · exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  · simp only [Set.mem_iInter,Set.mem_setOf_eq,inner_zero_left]
    exact fun _ => hc

theorem cube_projection_facet_interior (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hBunit : ∀i,‖B i‖=1) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (i : Fin 4) :
    c • B i∈intrinsicInterior ℝ (cubeFacet A i) := by
  have hself : inner ℝ (c • B i) (B i)=c := by
    rw [inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq,hBunit i]
    norm_num
  have hother : ∀j,j≠i → inner ℝ (c • B i) (B j)<c := by
    intro j hji
    have hh := (inner_lt_one_iff_real_of_norm_eq_one (hBunit i) (hBunit j)).mpr
      (fun h => hji (hBinj h).symm)
    rw [inner_smul_left,conj_trivial]
    exact (mul_lt_mul_of_pos_left hh hc).trans_eq (mul_one c)
  have hfacet : c • B i∈cubeFacet A i := by
    rw [cube_facet_halfspaces A B c hcross hstrict i]
    refine ⟨hself,fun j => ?_⟩
    by_cases hji : j=i
    · subst j;exact hself.le
    · exact (hother j hji).le
  let p : affineSpan ℝ (cubeFacet A i) := ⟨c • B i,subset_affineSpan ℝ _ hfacet⟩
  apply mem_intrinsicInterior.mpr
  refine ⟨p,?_,rfl⟩
  apply mem_interior.mpr
  refine ⟨⋂j : Fin 3,{x : affineSpan ℝ (cubeFacet A i) |
    inner ℝ (x : Point) (B (i.succAbove j))<c},?_,?_,?_⟩
  · intro x hx
    change (x : Point)∈cubeFacet A i
    apply (Set.ext_iff.mp (cube_facet_halfspaces A B c hcross hstrict i) (x : Point)).mpr
    have hi := cube_facet_span_plane A B c hcross i x.property
    refine ⟨hi,fun j => ?_⟩
    obtain rfl | ⟨k,rfl⟩ := Fin.eq_self_or_eq_succAbove i j
    · exact hi.le
    · exact (Set.mem_iInter.mp hx k).le
  · exact isOpen_iInter_of_finite (fun j =>
      isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const)
  · apply Set.mem_iInter.mpr
    intro j
    exact hother _ (Fin.succAbove_ne i j)

#print axioms cube_origin_interior
#print axioms cube_projection_facet_interior
end Blueprint.Thomson.Tail.Implementation
