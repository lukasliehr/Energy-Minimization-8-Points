import AllS.Units.N_GI.N_face_models.N_active_vertex_model
import AllS.Units.N_GI.N_face_models.N_edge_model
import AllS.Units.N_GI.N_face_models.N_isolated_vertex_model
import AllS.Units.N_GI.N_face_models.N_off_graph_model

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_models_local_polyhedral (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) (base : Point) :
    LocallySphericalPolyhedral (contactFaceRegion Y c base) := by
  intro p hp
  have hzero (U : Set Point) (hU : IsOpen U) (hpU : p ∈ U)
      (hmodel : ∀ y ∈ U, y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1) :
      ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧ ∃ n : ℕ, ∃ normal : Fin n → Point,
        ∀ y ∈ U, y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) y := by
    refine ⟨U, hU, hpU, 0, Fin.elim0, ?_⟩
    intro y hy
    rw [hmodel y hy]
    exact ⟨fun h => ⟨h, fun i => Fin.elim0 i⟩, And.left⟩
  by_cases hpG : p ∈ contactGraphTrace Y c
  · rcases contactGraphTrace_vertex_or_edge Y c hY p hpG with ⟨v, rfl⟩ | ⟨d, hd⟩
    · have hvu : ‖Y v‖ = 1 := hY.1 v
      by_cases hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c
      · obtain ⟨a, δ, hδ, hm⟩ := face_models_active_vertex_model Y c hY hc hcupper
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
      · obtain ⟨δ, hδ, hm⟩ := face_models_isolated_vertex_model Y c hY hc hbound base v hp hne
        exact hzero {y | δ < inner ℝ (Y v) y} (isOpen_lt continuous_const (by fun_prop))
          (by simpa [real_inner_self_eq_norm_sq, hvu] using hδ.2) hm
    · obtain ⟨n, hn, δ, hδ, hm⟩ := face_models_edge_model Y c hY hc hcupper hbound hirr
        base p d.1 d.2.val ⟨d.2.property.1.symm, d.2.property.2⟩ hp hd
      have hpu : ‖p‖ = 1 := closed_spherical_component_unit _ base p hp
      refine ⟨{y | δ < inner ℝ p y}, isOpen_lt continuous_const (by fun_prop), ?_, 1, fun _ => n, ?_⟩
      · simpa [real_inner_self_eq_norm_sq, hpu] using hδ.2
      · intro y hy
        rw [hm y hy]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 0⟩⟩
  · obtain ⟨U, hU, hpU, hm⟩ := face_models_off_graph_model Y c hY hc.1 base p hp hpG
    exact hzero U hU hpU hm

#print axioms face_models_local_polyhedral

end Blueprint.Thomson.Tail.Implementation
