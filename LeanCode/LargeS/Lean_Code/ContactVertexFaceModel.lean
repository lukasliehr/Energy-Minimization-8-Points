import Lean_Code.ContactSectorNeighborhoods
import Lean_Code.ComponentWedgeModel

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- At every nonisolated graph vertex on the closure of a complementary
component, that actual closure is locally exactly one consecutive closed
sector. This supplies the two-halfspace corner model without assuming a
simple boundary or a global face parametrization. -/
theorem contactFaceRegion_model_at_nonisolated_vertex (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : ℝ³) (v : Fin 8) (hv : Y v ∈ contactFaceRegion Y c base)
    (hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    ∃ a : ContactNeighbor Y c v, ∃ δ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ y : ℝ³, δ < inner ℝ (Y v) y →
        (y ∈ contactFaceRegion Y c base ↔ ‖y‖ = 1 ∧
          0 ≤ inner ℝ (crossVec (Y v) (Y a)) y ∧
          0 ≤ inner ℝ (crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)) y) := by
  classical
  have hvunit : ‖Y v‖ = 1 := hY.1 v
  let R := contactRotateAt Y c hY hc v
  let n₁ : ContactNeighbor Y c v → ℝ³ := fun a => crossVec (Y v) (Y a)
  let n₂ : ContactNeighbor Y c v → ℝ³ := fun a => crossVec (Y (R a)) (Y v)
  have hturn (a : ContactNeighbor Y c v) : 0 < inner ℝ (n₁ a) (Y (R a)) := by
    change 0 < inner ℝ (crossVec (Y v) (Y a)) (Y (R a))
    rw [triple_cyclic]
    exact contactRotateAt_triple_pos Y c hY hc hirr v a
  have hseps (a : ContactNeighbor Y c v) := contact_vertex_sector_separation Y c hY hc hcupper
    hbound hirr v a (R a) ⟨a.property.1.symm, a.property.2⟩
    ⟨(R a).property.1.symm, (R a).property.2⟩ (hturn a)
  choose t ht hsep using hseps
  obtain ⟨U₁, hU₁, hv₁, hempty⟩ := contactGraphTrace_local_sectors_empty Y c hY hc hbound hirr v
  obtain ⟨U₂, hU₂, hv₂, hcover⟩ := contact_strict_sectors_cover_locally Y c hY hc hirr v hne
  let V : Set ℝ³ := ⋂ a : ContactNeighbor Y c v, {y | t a < inner ℝ (Y v) y}
  have hV : IsOpen V := isOpen_iInter_of_finite (fun a => isOpen_lt continuous_const (by fun_prop))
  have hvV : Y v ∈ V := Set.mem_iInter.mpr (fun a => by
    change t a < inner ℝ (Y v) (Y v)
    simpa [real_inner_self_eq_norm_sq, hvunit] using (ht a).2)
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small (Y v) (hY.1 v) (U₁ ∩ U₂ ∩ V)
    ((hU₁.inter hU₂).inter hV) ⟨⟨hv₁, hv₂⟩, hvV⟩
  let W : Set ℝ³ := {y | δ < inner ℝ (Y v) y}
  have hW : IsOpen W := isOpen_lt continuous_const (by fun_prop)
  have hvW : Y v ∈ W := by simpa [W, real_inner_self_eq_norm_sq, hvunit] using hδ.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hvW)
  obtain ⟨x, hxF, hdist⟩ := Metric.mem_closure_iff.mp hv ε hε
  have hxW := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  have hxEnv : x ∈ openSphericalRegion (contactGraphTrace Y c)ᶜ := pathComponentIn_subset hxF
  have hxcap : x ∈ sphericalOpenCap (Y v) δ := ⟨hxEnv.1, hxW⟩
  obtain ⟨a, hx₁, hx₂⟩ := hcover x (hcap hxcap).1.2 hxEnv.1 hxEnv.2
  let d := Y a + Y (R a)
  have hd₁ : 0 < inner ℝ (n₁ a) d := by
    change 0 < inner ℝ (crossVec (Y v) (Y a)) (Y a + Y (R a))
    rw [inner_add_right, crossVec_inner_right, zero_add]
    exact hturn a
  have hd₂ : 0 < inner ℝ (n₂ a) d := by
    change 0 < inner ℝ (crossVec (Y (R a)) (Y v)) (Y a + Y (R a))
    rw [inner_add_right, crossVec_inner_left, add_zero, triple_cyclic]
    exact hturn a
  have hin (y : ℝ³) (hy : y ∈ sphericalOpenCap (Y v) δ)
      (hy₁ : 0 < inner ℝ (n₁ a) y) (hy₂ : 0 < inner ℝ (n₂ a) y) :
      y ∈ (contactGraphTrace Y c)ᶜ := hempty a y (hcap hy).1.1 hy₁ hy₂
  have hs (y : ℝ³) (hy : y ∈ sphericalOpenCap (Y v) δ)
      (hyN : inner ℝ (n₁ a) y < 0 ∨ inner ℝ (n₂ a) y < 0) :
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
    have hxt : x ∈ sphericalOpenCap (Y v) (t a) :=
      ⟨hxEnv.1, Set.mem_iInter.mp (hcap hxcap).2 a⟩
    have hyt : y ∈ sphericalOpenCap (Y v) (t a) :=
      ⟨hy.1, Set.mem_iInter.mp (hcap hy).2 a⟩
    exact hsep a x hxt y hyt hx₁ hx₂ hyN
  exact ⟨a, δ, hδ, component_wedge_local_model (contactGraphTrace Y c)ᶜ base (Y v)
    (n₁ a) (n₂ a) d δ hδ.1 hd₁ hd₂ hin x hxF hxcap hx₁ hx₂ hs⟩

end SquareAntiprismVerification
