import Lean_Code.ContactVertexFaceModel

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem contactGraphTrace_local_plane (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (v a : Fin 8) (ha : ContactAdj Y c v a) (p : ℝ³) (hp : p ∈ OpenContactArc (Y v) (Y a)) :
    ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U,
      x ∈ contactGraphTrace Y c ↔ ‖x‖ = 1 ∧ inner ℝ (crossVec (Y v) (Y a)) x = 0 := by
  classical
  let other : ContactDart Y c → Prop := fun d =>
    ¬((v = d.1 ∧ a = d.2.val) ∨ (v = d.2.val ∧ a = d.1))
  let B : Set ℝ³ := Set.range Y ∪ ⋃ d : {d : ContactDart Y c // other d},
    closedShortSphereArc (Y d.val.1) (Y d.val.2.val)
  have hB : IsCompact B := by
    apply (Set.finite_range Y).isCompact.union
    apply isCompact_iUnion
    intro d
    exact closedShortSphereArc_compact _ _ (hY.1 _) (hY.1 _)
      (contact_endpoints_nonantipodal _ _ (hY.1 _) c hc.1 d.val.2.property.2)
  have hpB : p ∉ B := by
    rintro (h | h)
    · obtain ⟨j, rfl⟩ := h
      exact contact_arc_avoids_vertices Y c hY hc hbound v a ha.1 ha.2 j hp
    · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
      rcases closedShortSphereArc_cases _ _ _ (hY.1 _) (hY.1 _) hd with h | h | h
      · rw [h] at hp
        exact contact_arc_avoids_vertices Y c hY hc hbound v a ha.1 ha.2 _ hp
      · rw [h] at hp
        exact contact_arc_avoids_vertices Y c hY hc hbound v a ha.1 ha.2 _ hp
      · exact Set.disjoint_left.mp (contact_graph_arcs_disjoint Y c hY hc hbound v a
          d.val.1 d.val.2.val ha.1 d.val.2.property.1.symm ha.2 d.val.2.property.2 d.property) hp h
  obtain ⟨V, hV, hpV, hplane⟩ := contact_arc_local_plane (Y v) (Y a) p c (hY.1 v) (hY.1 a) hc ha.2 hp
  refine ⟨V ∩ Bᶜ, hV.inter hB.isClosed.isOpen_compl, ⟨hpV, hpB⟩, ?_⟩
  intro x hx
  rw [← hplane x hx.1]
  constructor
  · rintro (h | h)
    · exact False.elim (hx.2 (Or.inl h))
    · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
      by_cases ho : other d
      · exact False.elim (hx.2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨d, ho⟩, hd⟩)))
      · have he : (v = d.1 ∧ a = d.2.val) ∨ (v = d.2.val ∧ a = d.1) := not_not.mp ho
        rcases he with he | he
        · simpa only [he.1, he.2] using hd
        · simpa only [he.1, he.2, closedShortSphereArc_comm (Y d.2.val) (Y d.1)] using hd
  · rintro ⟨r, hr, rfl⟩
    exact contactGraphTrace_arc Y c ⟨v, a, ha.1.symm, ha.2⟩ r hr

/-- At an interior contact-edge point, an actual face closure is locally
one of the two closed hemisides. The normal records which side it occupies. -/
theorem contactFaceRegion_model_at_edge (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base p : ℝ³) (v a : Fin 8) (ha : ContactAdj Y c v a)
    (hp : p ∈ contactFaceRegion Y c base) (hpedge : p ∈ OpenContactArc (Y v) (Y a)) :
    ∃ n : ℝ³, (n = crossVec (Y v) (Y a) ∨ n = -crossVec (Y v) (Y a)) ∧
      ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ y : ℝ³, δ < inner ℝ p y →
        (y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1 ∧ 0 ≤ inner ℝ n y) := by
  have hpu : ‖p‖ = 1 := closed_spherical_component_unit _ base p hp
  let n := crossVec (Y v) (Y a)
  obtain ⟨U₁, hU₁, hp₁, hplane⟩ := contactGraphTrace_local_plane Y c hY hc hbound v a ha p hpedge
  obtain ⟨U₂, hU₂, hp₂, hsep⟩ := contact_edge_sides_not_joined Y c hY hc hcupper hbound hirr v a ha p hpu hpedge
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small p hpu (U₁ ∩ U₂) (hU₁.inter hU₂) ⟨hp₁, hp₂⟩
  have hW : IsOpen {y : ℝ³ | δ < inner ℝ p y} := isOpen_lt continuous_const (by fun_prop)
  have hpW : δ < inner ℝ p p := by simpa [real_inner_self_eq_norm_sq, hpu] using hδ.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  obtain ⟨x, hxF, hdist⟩ := Metric.mem_closure_iff.mp hp ε hε
  have hxW := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  have hxEnv : x ∈ openSphericalRegion (contactGraphTrace Y c)ᶜ := pathComponentIn_subset hxF
  have hxcap : x ∈ sphericalOpenCap p δ := ⟨hxEnv.1, hxW⟩
  have hxne : inner ℝ n x ≠ 0 := fun h => hxEnv.2 ((hplane x (hcap hxcap).1).mpr ⟨hxEnv.1, h⟩)
  have hchoose : ∃ m : ℝ³, (m = n ∨ m = -n) ∧ 0 < inner ℝ m x := by
    by_cases hxpos : 0 < inner ℝ n x
    · exact ⟨n, Or.inl rfl, hxpos⟩
    · refine ⟨-n, Or.inr rfl, ?_⟩
      rw [inner_neg_left]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hxpos) hxne)
  obtain ⟨m, hm, hmx⟩ := hchoose
  have hmne : m ≠ 0 := by intro h; rw [h, inner_zero_left] at hmx; exact lt_irrefl _ hmx
  have hmm : 0 < inner ℝ m m := by rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hmne)
  have hin (y : ℝ³) (hy : y ∈ sphericalOpenCap p δ) (hy₁ : 0 < inner ℝ m y)
      (hy₂ : 0 < inner ℝ m y) : y ∈ (contactGraphTrace Y c)ᶜ := by
    intro hgraph
    have hyn : inner ℝ n y = 0 := ((hplane y (hcap hy).1).mp hgraph).2
    rcases hm with rfl | rfl
    · linarith
    · simp only [inner_neg_left, hyn, neg_zero] at hy₁
      exact lt_irrefl _ hy₁
  have hs (y : ℝ³) (hy : y ∈ sphericalOpenCap p δ)
      (hyN : inner ℝ m y < 0 ∨ inner ℝ m y < 0) :
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
    have hym : inner ℝ m y < 0 := hyN.elim id id
    rcases hm with rfl | rfl
    · exact hsep x (hcap hxcap).2 y (hcap hy).2 hmx hym
    · have hyp : 0 < inner ℝ n y := by simpa using hym
      have hxn : inner ℝ n x < 0 := by simpa using hmx
      exact fun hxy => hsep y (hcap hy).2 x (hcap hxcap).2 hyp hxn hxy.symm
  refine ⟨m, hm, δ, hδ, ?_⟩
  intro y hy
  simpa only [and_self, contactFaceRegion] using component_wedge_local_model (contactGraphTrace Y c)ᶜ base p m m m
    δ hδ.1 hmm hmm hin x hxF hxcap hmx hmx hs y hy

end SquareAntiprismVerification
