import Lean_Code.ContactEdgeFaceModel
import Lean_Code.PuncturedSphericalCaps

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem contactFaceRegion_model_at_isolated_vertex (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (base : ℝ³) (v : Fin 8) (hv : Y v ∈ contactFaceRegion Y c base)
    (hiso : ¬∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ y : ℝ³, δ < inner ℝ (Y v) y →
      (y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1) := by
  have hvu : ‖Y v‖ = 1 := hY.1 v
  obtain ⟨U, hU, hvU, hstar⟩ := contactGraphTrace_local_star Y c hY hc hbound v
  have hpoint (y : ℝ³) (hy : y ∈ U) : y ∈ contactGraphTrace Y c ↔ y = Y v := by
    rw [hstar y hy]
    constructor
    · rintro (h | ⟨j, hj⟩)
      · exact h
      · exact False.elim (hiso ⟨j, j.property⟩)
    · exact Or.inl
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small (Y v) hvu U hU hvU
  have hW : IsOpen {y : ℝ³ | δ < inner ℝ (Y v) y} := isOpen_lt continuous_const (by fun_prop)
  have hvW : δ < inner ℝ (Y v) (Y v) := by simpa [real_inner_self_eq_norm_sq, hvu] using hδ.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hvW)
  obtain ⟨x, hxF, hdist⟩ := Metric.mem_closure_iff.mp hv ε hε
  have hxW := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  have hxEnv : x ∈ openSphericalRegion (contactGraphTrace Y c)ᶜ := pathComponentIn_subset hxF
  have hxcap : x ∈ sphericalOpenCap (Y v) δ := ⟨hxEnv.1, hxW⟩
  have hxv : x ≠ Y v := fun h => hxEnv.2 ((hpoint x (hcap hxcap)).mpr h)
  refine ⟨δ, hδ, ?_⟩
  intro y hyW
  constructor
  · exact fun hy => closed_spherical_component_unit _ base y hy
  · intro hyu
    by_cases hyv : y = Y v
    · exact hyv ▸ hv
    · have hycap : y ∈ sphericalOpenCap (Y v) δ := ⟨hyu, hyW⟩
      obtain ⟨γ, hγ⟩ := punctured_spherical_cap_joined (Y v) hvu δ hδ x y hxcap hycap hxv hyv
      have hxy : JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
        refine ⟨γ, fun t => ⟨(hγ t).1.1, ?_⟩⟩
        intro hgraph
        exact (hγ t).2 ((hpoint _ (hcap (hγ t).1)).mp hgraph)
      exact subset_closure (hxF.trans hxy)

lemma contactGraphTrace_vertex_or_edge (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (p : ℝ³) (hp : p ∈ contactGraphTrace Y c) :
    (∃ v, p = Y v) ∨ ∃ d : ContactDart Y c, p ∈ OpenContactArc (Y d.1) (Y d.2.val) := by
  rcases hp with h | h
  · obtain ⟨v, rfl⟩ := h
    exact Or.inl ⟨v, rfl⟩
  · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
    rcases closedShortSphereArc_cases _ _ _ (hY.1 _) (hY.1 _) hd with h | h | h
    · exact Or.inl ⟨d.1, h⟩
    · exact Or.inl ⟨d.2.val, h⟩
    · exact Or.inr ⟨d, h⟩

/-- Actual complementary face closures have local models with zero, one,
or two great-circle halfspaces. This is now a theorem about the defined
regions, not an extra interface assumption. -/
theorem contactFaceRegion_locally_spherical_polyhedral (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) (base : ℝ³) :
    LocallySphericalPolyhedral (contactFaceRegion Y c base) := by
  intro p hp
  have hzero (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U)
      (hmodel : ∀ y ∈ U, y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1) :
      ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∃ n : ℕ, ∃ normal : Fin n → ℝ³,
        ∀ y ∈ U, y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) y := by
    refine ⟨U, hU, hpU, 0, Fin.elim0, ?_⟩
    intro y hy
    rw [hmodel y hy]
    exact ⟨fun h => ⟨h, fun i => Fin.elim0 i⟩, And.left⟩
  by_cases hpG : p ∈ contactGraphTrace Y c
  · rcases contactGraphTrace_vertex_or_edge Y c hY p hpG with ⟨v, rfl⟩ | ⟨d, hd⟩
    · have hvu : ‖Y v‖ = 1 := hY.1 v
      by_cases hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c
      · obtain ⟨a, δ, hδ, hm⟩ := contactFaceRegion_model_at_nonisolated_vertex Y c hY hc hcupper
          hbound hirr base v hp hne
        let n₁ := crossVec (Y v) (Y a)
        let n₂ := crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)
        refine ⟨{y | δ < inner ℝ (Y v) y}, isOpen_lt continuous_const (by fun_prop), ?_, 2, ![n₁, n₂], ?_⟩
        · simpa [real_inner_self_eq_norm_sq, hvu] using hδ.2
        · intro y hy
          rw [hm y hy]
          constructor
          · rintro ⟨hu, h₁, h₂⟩
            refine ⟨hu, ?_⟩
            intro i
            fin_cases i
            · exact h₁
            · exact h₂
          · rintro ⟨hu, hN⟩
            exact ⟨hu, hN 0, hN 1⟩
      · obtain ⟨δ, hδ, hm⟩ := contactFaceRegion_model_at_isolated_vertex Y c hY hc hbound base v hp hne
        exact hzero {y | δ < inner ℝ (Y v) y} (isOpen_lt continuous_const (by fun_prop))
          (by simpa [real_inner_self_eq_norm_sq, hvu] using hδ.2) hm
    · obtain ⟨n, hn, δ, hδ, hm⟩ := contactFaceRegion_model_at_edge Y c hY hc hcupper hbound hirr
        base p d.1 d.2.val ⟨d.2.property.1.symm, d.2.property.2⟩ hp hd
      have hpu : ‖p‖ = 1 := closed_spherical_component_unit _ base p hp
      refine ⟨{y | δ < inner ℝ p y}, isOpen_lt continuous_const (by fun_prop), ?_, 1, fun _ => n, ?_⟩
      · simpa [real_inner_self_eq_norm_sq, hpu] using hδ.2
      · intro y hy
        rw [hm y hy]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 0⟩⟩
  · obtain ⟨U, hU, hpU, hm⟩ := contactFaceRegion_model_off_graph Y c hY hc.1 base p hp hpG
    exact hzero U hU hpU hm

/-- The compact locally convex face regions are globally shorter-arc
convex. The actual-face hypotheses are all discharged here. -/
theorem contactFaceRegion_shortArcClosed (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : ℝ³) (hbase : ‖base‖ = 1) (hbaseG : base ∉ contactGraphTrace Y c) :
    ShortArcClosed (contactFaceRegion Y c base) := by
  letI : PreconnectedSpace (contactFaceRegion Y c base) :=
    isPreconnected_iff_preconnectedSpace.mp (contactFaceRegion_preconnected Y c base hbase hbaseG)
  exact shortArcClosed_of_compact_local_models (contactFaceRegion_compact Y c base)
    (contactFaceRegion_locally_spherical_polyhedral Y c hY hc hcupper hbound hirr base)
    (contactFaceRegion_dense_interior Y c hY hc.1 base)

end SquareAntiprismVerification
