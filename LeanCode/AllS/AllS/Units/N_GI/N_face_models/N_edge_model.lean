import AllS.Units.N_G.N_setup
import Lean_Code.ContactFaceLocalModels
import AllS.Units.N_GI.N_sector_separation.N_edge_sides

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_models_edge_model (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base p : Point) (v a : Fin 8) (ha : ContactAdj Y c v a)
    (hp : p ∈ contactFaceRegion Y c base) (hpedge : p ∈ OpenContactArc (Y v) (Y a)) :
    ∃ n : Point, (n = crossVec (Y v) (Y a) ∨ n = -crossVec (Y v) (Y a)) ∧
      ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ y : Point, δ < inner ℝ p y →
        (y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1 ∧ 0 ≤ inner ℝ n y) := by
  have hpu : ‖p‖ = 1 := closed_spherical_component_unit _ base p hp
  let n := crossVec (Y v) (Y a)
  obtain ⟨U₁, hU₁, hp₁, hplane⟩ := contactGraphTrace_local_plane Y c hY hc hbound v a ha p hpedge
  obtain ⟨U₂, hU₂, hp₂, hsep⟩ := sector_separation_edge_sides Y c hY hc hcupper hbound hirr v a ha p hpu hpedge
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small p hpu (U₁ ∩ U₂) (hU₁.inter hU₂) ⟨hp₁, hp₂⟩
  have hW : IsOpen {y : Point | δ < inner ℝ p y} := isOpen_lt continuous_const (by fun_prop)
  have hpW : δ < inner ℝ p p := by simpa [real_inner_self_eq_norm_sq, hpu] using hδ.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  obtain ⟨x, hxF, hdist⟩ := Metric.mem_closure_iff.mp hp ε hε
  have hxW := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  have hxEnv : x ∈ openSphericalRegion (contactGraphTrace Y c)ᶜ := pathComponentIn_subset hxF
  have hxcap : x ∈ sphericalOpenCap p δ := ⟨hxEnv.1, hxW⟩
  have hxne : inner ℝ n x ≠ 0 := fun h => hxEnv.2 ((hplane x (hcap hxcap).1).mpr ⟨hxEnv.1, h⟩)
  have hchoose : ∃ m : Point, (m = n ∨ m = -n) ∧ 0 < inner ℝ m x := by
    by_cases hxpos : 0 < inner ℝ n x
    · exact ⟨n, Or.inl rfl, hxpos⟩
    · refine ⟨-n, Or.inr rfl, ?_⟩
      rw [inner_neg_left]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hxpos) hxne)
  obtain ⟨m, hm, hmx⟩ := hchoose
  have hmne : m ≠ 0 := by intro h; rw [h, inner_zero_left] at hmx; exact lt_irrefl _ hmx
  have hmm : 0 < inner ℝ m m := by rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hmne)
  have hin (y : Point) (hy : y ∈ sphericalOpenCap p δ) (hy₁ : 0 < inner ℝ m y)
      (hy₂ : 0 < inner ℝ m y) : y ∈ (contactGraphTrace Y c)ᶜ := by
    intro hgraph
    have hyn : inner ℝ n y = 0 := ((hplane y (hcap hy).1).mp hgraph).2
    rcases hm with rfl | rfl
    · linarith
    · simp only [inner_neg_left, hyn, neg_zero] at hy₁
      exact lt_irrefl _ hy₁
  have hs (y : Point) (hy : y ∈ sphericalOpenCap p δ)
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

#print axioms face_models_edge_model

end Blueprint.Thomson.Tail.Implementation
