import AllS.Units.N_GI.N_boundary_support.N_initial_left_face

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_support_next_dart (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : Point) (hbase : ‖base‖ = 1) (hbaseG : base ∉ contactGraphTrace Y c)
    (d : ContactDart Y c) (hs : FaceSupportsDart Y c (contactFaceRegion Y c base) d) :
    FaceSupportsDart Y c (contactFaceRegion Y c base) (contactFaceNext Y c hY hc d) := by
  let D := contactFaceRegion Y c base
  let v := d.2.val
  let a := d.1
  let R := contactRotateAt Y c hY hc v
  have hvu : ‖Y v‖ = 1 := hY.1 v
  have hunit : ∀ x ∈ D, ‖x‖ = 1 := closed_spherical_component_unit _ base
  have hconv : ShortArcClosed D := face_convex_short_arc_closed Y c hY hc hcupper hbound hirr base hbase hbaseG
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
  obtain ⟨u, δ, hδ, hm⟩ := face_models_active_vertex_model Y c hY hc hcupper
    hbound hirr base v hvD ⟨k, k.property⟩
  let n₁ := crossVec (Y v) (Y u)
  let n₂ := crossVec (Y (R u)) (Y v)
  let U : Set Point := {x | δ < inner ℝ (Y v) x}
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
    · let normal : Bool → Point := fun i => if i then n₁ else n₂
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
  have hedge := boundary_support_edge_propagation Y c hY hc hcupper hbound hirr base v u
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

#print axioms boundary_support_next_dart

end Blueprint.Thomson.Tail.Implementation
