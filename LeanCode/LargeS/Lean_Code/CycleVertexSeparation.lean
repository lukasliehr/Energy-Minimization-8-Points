import Lean_Code.SphericalWedgePaths

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma contact_arc_point_near_left (a b n : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : 0 < c) (hab : inner ℝ a b = c)
    (hna : inner ℝ n a = 0) (hnb : 0 < inner ℝ n b)
    (U : Set ℝ³) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ q ∈ U, ‖q‖ = 1 ∧ q ∈ OpenContactArc a b ∧ 0 < inner ℝ n q := by
  have hanti := contact_endpoints_nonantipodal a b hb c hc hab
  have hnear : {r | shortSphereArc a b r ∈ U} ∈ nhds (0 : ℝ) :=
    (shortSphereArc_continuousAt a b ha hb hanti 0 ⟨le_rfl, zero_le_one⟩)
      (by simpa only [shortSphereArc_zero a b ha] using hU.mem_nhds haU)
  obtain ⟨r, hrU, hr0, hr1⟩ := exists_small_positive_in_neighborhood _ hnear 1 zero_lt_one
  refine ⟨shortSphereArc a b r, hrU, shortSphereArc_unit a b ha hb hanti r ⟨hr0.le, hr1.le⟩,
    ⟨r, hr0, hr1, rfl⟩, ?_⟩
  apply sphereNormalize_inner_pos
  simp only [inner_add_right, inner_smul_right, hna, mul_zero, zero_add]
  exact mul_pos hr0 hnb

namespace SimpleContactCycle

/-- The two local sectors at a strictly turning vertex of an embedded
contact cycle cannot be joined in the complement of that entire cycle. -/
theorem vertex_sectors_not_joined {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (k : Fin (C.size + 2))
    (hturn : 0 < inner ℝ (crossVec (Y (C.vertex k)) (Y (C.vertex (C.next k))))
      (Y (C.vertex (C.next.symm k)))) :
    let n₁ := crossVec (Y (C.vertex k)) (Y (C.vertex (C.next k)))
    let n₂ := crossVec (Y (C.vertex (C.next.symm k))) (Y (C.vertex k))
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x ∈ sphericalOpenCap (Y (C.vertex k)) δ,
      ∀ y ∈ sphericalOpenCap (Y (C.vertex k)) δ,
        0 < inner ℝ n₁ x → 0 < inner ℝ n₂ x →
        (inner ℝ n₁ y < 0 ∨ inner ℝ n₂ y < 0) →
        ¬JoinedIn (openSphericalRegion (cycleArcTrace C.next (Y ∘ C.vertex))ᶜ) x y := by
  let v := Y (C.vertex k)
  let a := Y (C.vertex (C.next k))
  let b := Y (C.vertex (C.next.symm k))
  let n₁ := crossVec v a
  let n₂ := crossVec b v
  let T := cycleArcTrace C.next (Y ∘ C.vertex)
  have hv : ‖v‖ = 1 := hY.1 _
  have hn₁v : inner ℝ n₁ v = 0 := crossVec_inner_left v a
  have hn₁a : inner ℝ n₁ a = 0 := crossVec_inner_right v a
  have hn₂v : inner ℝ n₂ v = 0 := crossVec_inner_right b v
  have hn₂b : inner ℝ n₂ b = 0 := crossVec_inner_left b v
  have hturn' : 0 < inner ℝ n₂ a := by
    change 0 < inner ℝ (crossVec b v) a
    rw [triple_cyclic b v a]
    exact hturn
  have hn₁ne : n₁ ≠ 0 := by
    intro h
    have hh : 0 < inner ℝ n₁ b := hturn
    rw [h, inner_zero_left] at hh
    exact lt_irrefl _ hh
  obtain ⟨U, hU, hvU, hmodel⟩ := C.trace_local_wedge hY hc hbound k hturn
  obtain ⟨δ, hδ, hcapU⟩ := sphericalOpenCap_small v hv U hU hvU
  have htrace (x : ℝ³) (hx : x ∈ sphericalOpenCap v δ) :
      x ∈ T ↔ x ∈ sphericalWedgeTrace n₁ n₂ := by
    have hh := hmodel x (hcapU hx)
    change (x ∈ T ↔ ‖x‖ = 1 ∧ x ∈ sphericalWedgeTrace n₁ n₂) at hh
    exact hh.trans ⟨And.right, fun h => ⟨hx.1, h⟩⟩
  let V : Set ℝ³ := {x | δ < inner ℝ v x}
  have hV : IsOpen V := isOpen_lt continuous_const (by fun_prop)
  have hvV : v ∈ V := by simpa [V, real_inner_self_eq_norm_sq, hv] using hδ.2
  let normal : Bool → ℝ³ := fun i => if i then -n₁ else -n₂
  have hpN : ∀ i, inner ℝ (normal i) v = 0 := by
    intro i; cases i <;> simp [normal, hn₁v, hn₂v]
  have hdN : ∀ i, 0 < inner ℝ (normal i) (-(a + b)) := by
    intro i; cases i
    · simpa [normal, inner_add_right, hn₂b] using hturn'
    · have hh : 0 < inner ℝ n₁ b := hturn
      simpa [normal, inner_add_right, hn₁a] using hh
  obtain ⟨z, hzV, hzu, hzN⟩ := unit_nearby_strict_normals normal v (-(a + b)) hv hpN hdN V hV hvV
  have hz₁ : inner ℝ n₁ z < 0 := by simpa [normal] using hzN true
  have hz₂ : inner ℝ n₂ z < 0 := by simpa [normal] using hzN false
  obtain ⟨q, hqV, hqu, hqedge, hq₂⟩ := contact_arc_point_near_left v a n₂ c hv (hY.1 _) hc.1
    (C.adjacent k).2 hn₂v hturn' V hV hvV
  have hq₁ : inner ℝ n₁ q = 0 := by
    obtain ⟨r, hr0, hr1, hr⟩ := hqedge
    rw [hr]
    change inner ℝ n₁ (sphereNormalize ((1 - r) • v + r • a)) = 0
    simp only [sphereNormalize_inner, inner_add_right, inner_smul_right, hn₁v, hn₁a,
      mul_zero, add_zero]
  obtain ⟨E, hE, hqE, hsep⟩ := cycle_edge_sides_not_joined C.next (Y ∘ C.vertex) c
    (fun i => hY.1 _) hc (fun i => (C.adjacent i).2) k q hqu hqedge
    (C.edge_avoids_other_edges hY hc hbound k q hqedge)
  let W := E ∩ V ∩ {x : ℝ³ | 0 < inner ℝ n₂ x}
  have hW : IsOpen W := (hE.inter hV).inter (isOpen_lt continuous_const (by fun_prop))
  have hqW : q ∈ W := ⟨⟨hqE, hqV⟩, hq₂⟩
  obtain ⟨x₀, hxW, y₀, hyW, hxu, hyu, hx₁, hy₁⟩ :=
    unit_both_sides_in_open q n₁ hqu hn₁ne hq₁ W hW hqW
  have href : ¬JoinedIn (openSphericalRegion Tᶜ) x₀ y₀ :=
    hsep x₀ hxW.1.1 y₀ hyW.1.1 hx₁ hy₁
  exact ⟨δ, hδ, cap_wedge_separation T v n₁ n₂ δ hδ.1 htrace z ⟨hzu, hzV⟩ hz₁ hz₂
    x₀ y₀ ⟨hxu, hxW.1.2⟩ ⟨hyu, hyW.1.2⟩ hx₁ hxW.2 (Or.inl hy₁) href⟩

lemma next_symm_zero {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c) :
    C.next.symm 0 = Fin.last (C.size + 1) := by
  apply C.next.injective
  simp [next_apply]

end SimpleContactCycle

/-- A sector between two positively oriented contact rays is separated
from its exterior by an actual simple contact cycle. In particular, this
applies to every consecutive sector of the rotation system. -/
theorem contact_vertex_sector_separation (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (v a b : Fin 8) (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b)
    (hturn : 0 < inner ℝ (crossVec (Y v) (Y a)) (Y b)) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x ∈ sphericalOpenCap (Y v) δ, ∀ y ∈ sphericalOpenCap (Y v) δ,
        0 < inner ℝ (crossVec (Y v) (Y a)) x →
        0 < inner ℝ (crossVec (Y b) (Y v)) x →
        (inner ℝ (crossVec (Y v) (Y a)) y < 0 ∨
          inner ℝ (crossVec (Y b) (Y v)) y < 0) →
        ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
  have hab : a ≠ b := by
    intro h
    rw [h, crossVec_inner_right] at hturn
    exact lt_irrefl _ hturn
  obtain ⟨C, hv, ha', hb'⟩ := simple_contact_cycle_through_neighbors Y c hY.1 hc.1 hcupper
    hirr v a b ha hb hab
  have hnext : C.vertex (C.next 0) = a := by simpa only [SimpleContactCycle.next_apply, zero_add] using ha'
  have hprev : C.vertex (C.next.symm 0) = b := by rw [C.next_symm_zero]; exact hb'
  have ht : 0 < inner ℝ (crossVec (Y (C.vertex 0)) (Y (C.vertex (C.next 0))))
      (Y (C.vertex (C.next.symm 0))) := by simpa only [hv, hnext, hprev] using hturn
  obtain ⟨δ, hδ, hsep⟩ := C.vertex_sectors_not_joined hY hc hbound 0 ht
  simp only [hv, hnext, hprev] at hsep
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hx₁ hx₂ hyN hjoined
  apply hsep x hx y hy hx₁ hx₂ hyN
  obtain ⟨γ, hγ⟩ := hjoined
  refine ⟨γ, fun t => ⟨(hγ t).1, ?_⟩⟩
  intro htrace
  exact (hγ t).2 (C.trace_subset_graph htrace)

end SquareAntiprismVerification
