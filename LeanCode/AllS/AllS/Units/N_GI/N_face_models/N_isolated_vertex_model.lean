import AllS.Units.N_G.N_setup
import Lean_Code.ContactFaceLocalModels

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_models_isolated_vertex_model (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (base : Point) (v : Fin 8) (hv : Y v ∈ contactFaceRegion Y c base)
    (hiso : ¬∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ y : Point, δ < inner ℝ (Y v) y →
      (y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1) := by
  have hvu : ‖Y v‖ = 1 := hY.1 v
  obtain ⟨U, hU, hvU, hstar⟩ := contactGraphTrace_local_star Y c hY hc hbound v
  have hpoint (y : Point) (hy : y ∈ U) : y ∈ contactGraphTrace Y c ↔ y = Y v := by
    rw [hstar y hy]
    constructor
    · rintro (h | ⟨j, hj⟩)
      · exact h
      · exact False.elim (hiso ⟨j, j.property⟩)
    · exact Or.inl
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small (Y v) hvu U hU hvU
  have hW : IsOpen {y : Point | δ < inner ℝ (Y v) y} := isOpen_lt continuous_const (by fun_prop)
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

#print axioms face_models_isolated_vertex_model

end Blueprint.Thomson.Tail.Implementation
