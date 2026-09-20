import Lean_Code.FaceEdgePropagation

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def FaceSupportsDart (Y : Fin 8 → ℝ³) (c : ℝ) (D : Set ℝ³) (d : ContactDart Y c) : Prop :=
  (∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (Y d.1) (Y d.2.val) r ∈ D) ∧
    ∀ x ∈ D, 0 ≤ inner ℝ (crossVec (Y d.1) (Y d.2.val)) x

lemma global_halfspace_of_open_local_support (D : Set ℝ³)
    (hunit : ∀ x ∈ D, ‖x‖ = 1) (hconv : ShortArcClosed D)
    (p n : ℝ³) (hp : p ∈ D) (hplane : inner ℝ n p = 0)
    (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U)
    (hlocal : ∀ x ∈ D, x ∈ U → 0 ≤ inner ℝ n x) : ∀ x ∈ D, 0 ≤ inner ℝ n x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  exact global_halfspace_of_local_support D hunit hconv p n hp hplane
    ⟨ε, hε, fun x hx hdist => hlocal x hx (hball hdist)⟩

lemma contact_ray_in_empty_closed_wedge (p u w a : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (ha : ‖a‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpu : inner ℝ p u = c) (hpw : inner ℝ p w = c) (hpa : inner ℝ p a = c)
    (hturn : 0 < inner ℝ (crossVec p u) w)
    (h₁ : 0 ≤ inner ℝ (crossVec p u) a) (h₂ : 0 ≤ inner ℝ (crossVec w p) a)
    (hempty : ¬(0 < inner ℝ (crossVec p u) a ∧ 0 < inner ℝ (crossVec w p) a)) :
    a = u ∨ a = w := by
  by_cases hz₁ : inner ℝ (crossVec p u) a = 0
  · apply Or.inl
    apply supporting_contact_ray_unique p u w a c hp hu ha hc hpu hpa hturn hz₁
    rwa [← triple_cyclic w p a]
  · have hz₂ : inner ℝ (crossVec w p) a = 0 := by
      by_contra h
      exact hempty ⟨lt_of_le_of_ne h₁ (Ne.symm hz₁), lt_of_le_of_ne h₂ (Ne.symm h)⟩
    apply Or.inr
    apply supporting_contact_ray_unique p w (-u) a c hp hw ha hc hpw hpa
    · rw [inner_neg_right, triple_swap_last p w u, neg_neg]
      exact hturn
    · rw [crossVec_swap w p, inner_neg_left, hz₂, neg_zero]
    · rw [inner_neg_right, triple_swap_last p a u, neg_neg]
      exact h₁

/-- Following the boundary permutation preserves one fixed supporting
face. Its incoming ray must be the second boundary ray of the local sector:
the first alternative contradicts the known left-side support. -/
theorem face_supports_next_dart (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : ℝ³) (hbase : ‖base‖ = 1) (hbaseG : base ∉ contactGraphTrace Y c)
    (d : ContactDart Y c) (hs : FaceSupportsDart Y c (contactFaceRegion Y c base) d) :
    FaceSupportsDart Y c (contactFaceRegion Y c base) (contactFaceNext Y c hY hc d) := by
  let D := contactFaceRegion Y c base
  let v := d.2.val
  let a := d.1
  let R := contactRotateAt Y c hY hc v
  have hvu : ‖Y v‖ = 1 := hY.1 v
  have hunit : ∀ x ∈ D, ‖x‖ = 1 := closed_spherical_component_unit _ base
  have hconv : ShortArcClosed D := contactFaceRegion_shortArcClosed Y c hY hc hcupper hbound hirr base hbase hbaseG
  have hvD : Y v ∈ D := by
    have hh := hs.1 1 ⟨zero_le_one, le_rfl⟩
    change shortSphereArc (Y a) (Y v) 1 ∈ D at hh
    rwa [shortSphereArc_one _ _ hvu] at hh
  have haD : Y a ∈ D := by
    have hh := hs.1 0 ⟨le_rfl, zero_le_one⟩
    change shortSphereArc (Y a) (Y v) 0 ∈ D at hh
    rwa [shortSphereArc_zero _ _ (hY.1 a)] at hh
  let k : ContactNeighbor Y c v := ⟨a, d.2.property.1.symm,
    (real_inner_comm (Y a) (Y v)).trans d.2.property.2⟩
  obtain ⟨u, δ, hδ, hm⟩ := contactFaceRegion_model_at_nonisolated_vertex Y c hY hc hcupper
    hbound hirr base v hvD ⟨k, k.property⟩
  let n₁ := crossVec (Y v) (Y u)
  let n₂ := crossVec (Y (R u)) (Y v)
  let U : Set ℝ³ := {x | δ < inner ℝ (Y v) x}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hvU : Y v ∈ U := by simpa [U, real_inner_self_eq_norm_sq, hvu] using hδ.2
  have hn₁ : ∀ x ∈ D, 0 ≤ inner ℝ n₁ x :=
    global_halfspace_of_open_local_support D hunit hconv (Y v) n₁ hvD (crossVec_inner_left _ _)
      U hU hvU (fun x hx hxU => ((hm x hxU).mp hx).2.1)
  have hn₂ : ∀ x ∈ D, 0 ≤ inner ℝ n₂ x :=
    global_halfspace_of_open_local_support D hunit hconv (Y v) n₂ hvD (crossVec_inner_right _ _)
      U hU hvU (fun x hx hxU => ((hm x hxU).mp hx).2.2)
  have hturn : 0 < inner ℝ n₁ (Y (R u)) := by
    change 0 < inner ℝ (crossVec (Y v) (Y u)) (Y (R u))
    rw [triple_cyclic]
    exact contactRotateAt_triple_pos Y c hY hc hirr v u
  have hturn' : 0 < inner ℝ n₂ (Y u) := by
    change 0 < inner ℝ (crossVec (Y (R u)) (Y v)) (Y u)
    rw [triple_cyclic]
    exact hturn
  have haCases : a = u.val ∨ a = (R u).val := by
    have hh := contact_ray_in_empty_closed_wedge (Y v) (Y u) (Y (R u)) (Y a) c
      hvu (hY.1 _) (hY.1 _) (hY.1 _) hc u.property.2 (R u).property.2 k.property.2
      hturn (hn₁ _ haD) (hn₂ _ haD) (contactRotateAt_sector_empty Y c hY hc hbound hirr v u k)
    rcases hh with hh | hh
    · exact Or.inl (hY.2 hh)
    · exact Or.inr (hY.2 hh)
  have haLast : a = (R u).val := by
    rcases haCases with haFirst | haLast
    · let normal : Bool → ℝ³ := fun i => if i then n₁ else n₂
      have hpN : ∀ i, inner ℝ (normal i) (Y v) = 0 := by
        intro i; cases i
        · exact crossVec_inner_right _ _
        · exact crossVec_inner_left _ _
      have hdN : ∀ i, 0 < inner ℝ (normal i) (Y u + Y (R u)) := by
        intro i; cases i
        · change 0 < inner ℝ n₂ (Y u + Y (R u))
          rw [inner_add_right, show inner ℝ n₂ (Y (R u)) = 0 from crossVec_inner_left _ _, add_zero]
          exact hturn'
        · change 0 < inner ℝ n₁ (Y u + Y (R u))
          rw [inner_add_right, show inner ℝ n₁ (Y u) = 0 from crossVec_inner_right _ _, zero_add]
          exact hturn
      obtain ⟨z, hzU, hzu, hzN⟩ := unit_nearby_strict_normals normal (Y v) (Y u + Y (R u))
        hvu hpN hdN U hU hvU
      have hzD : z ∈ D := (hm z hzU).mpr ⟨hzu, (hzN true).le, (hzN false).le⟩
      have hh := hs.2 z hzD
      change 0 ≤ inner ℝ (crossVec (Y a) (Y v)) z at hh
      rw [haFirst, crossVec_swap, inner_neg_left] at hh
      have hzpos : 0 < inner ℝ (crossVec (Y v) (Y u)) z := hzN true
      exact False.elim (by linarith)
    · exact haLast
  have hnext : (contactFaceNext Y c hY hc d).2.val = u.val := by
    have hk : k = R u := Subtype.ext haLast
    change (R.symm k).val = u.val
    rw [hk, Equiv.symm_apply_apply]
  obtain ⟨q, hqU, hqu, hqedge, hq₂⟩ := contact_arc_point_near_left (Y v) (Y u) n₂ c hvu (hY.1 _)
    hc.1 u.property.2 (crossVec_inner_right _ _) hturn' U hU hvU
  have hq₁ : inner ℝ n₁ q = 0 := by
    obtain ⟨r, hr0, hr1, hr⟩ := hqedge
    have heq : shortSphereArc (Y v) (Y u) r = q := hr.symm
    rw [← heq]
    exact shortSphereArc_plane (Y v) (Y u) r
  have hqD : q ∈ D := (hm q hqU).mpr ⟨hqu, hq₁.ge, hq₂.le⟩
  have hedge := contact_edge_in_face_of_interior Y c hY hc hcupper hbound hirr base v u
    ⟨u.property.1.symm, u.property.2⟩ q hqD hqedge
  constructor
  · intro r hr
    change shortSphereArc (Y v) (Y (contactFaceNext Y c hY hc d).2.val) r ∈ D
    rw [hnext]
    exact hedge r hr
  · intro x hx
    change 0 ≤ inner ℝ (crossVec (Y v) (Y (contactFaceNext Y c hY hc d).2.val)) x
    rw [hnext]
    exact hn₁ x hx

end SquareAntiprismVerification
