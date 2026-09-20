import Lean_Code.GreatCircleShortening

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A compact parameter set gives one neighborhood working for all parameters.
This is the elementary finite-subcover form of the tube argument. -/
lemma compact_parameter_neighborhood {X T Z : Type*}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
    (f : X × T → Z) (a : X) (K : Set T) (hK : IsCompact K)
    (U : Set Z) (hU : IsOpen U)
    (hcont : ∀ t ∈ K, ContinuousAt f (a, t))
    (hmem : ∀ t ∈ K, f (a, t) ∈ U) :
    ∃ V ∈ nhds a, ∀ b ∈ V, ∀ t ∈ K, f (b, t) ∈ U := by
  classical
  have hrect : ∀ t : K, ∃ V W, V ∈ nhds a ∧ IsOpen W ∧ t.val ∈ W ∧
      ∀ b ∈ V, ∀ s ∈ W, f (b, s) ∈ U := by
    intro t
    have h := hcont t.val t.property (hU.mem_nhds (hmem t.val t.property))
    rw [nhds_prod_eq] at h
    obtain ⟨V, hV, W, hW, hsub⟩ := Filter.mem_prod_iff.mp h
    obtain ⟨W', hW'W, hW'o, htW'⟩ := mem_nhds_iff.mp hW
    refine ⟨V, W', hV, hW'o, htW', ?_⟩
    intro b hb s hs
    exact hsub ⟨hb, hW'W hs⟩
  choose V W hV hWo htW hrect using hrect
  have hcover : K ⊆ ⋃ t : K, W t := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, htW ⟨t, ht⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W hWo hcover
  have hevent : ∀ᶠ b in nhds a, ∀ t ∈ I, b ∈ V t := by
    clear hI
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      filter_upwards [hV i, ih] with b hb hrest
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hb
      · exact hrest t ht
  refine ⟨{b | ∀ t ∈ I, b ∈ V t}, hevent, ?_⟩
  intro b hb t ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI ht)
  obtain ⟨hiI, hti⟩ := Set.mem_iUnion.mp hi
  exact hrect i b (hb i hiI) t hti

lemma shortSphereArc_joint_continuousAt (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun q : ℝ³ × ℝ => shortSphereArc a q.1 q.2) (b, t) := by
  let f : ℝ³ × ℝ → ℝ³ := fun q => (1 - q.2) • a + q.2 • q.1
  have hf : ContinuousAt f (b, t) := by dsimp [f]; fun_prop
  exact ContinuousAt.comp (f := f) (sphereNormalize_continuousAt _
    (shortSphereArc_combination_ne_zero a b ha hb hanti t ht)) hf

/-- Every point of a nonantipodal shorter arc stays in an open region when
one endpoint is moved sufficiently little. This proves the required uniform
containment, not merely continuity at its midpoint. -/
theorem shortSphereArc_stable_in_open (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (U : Set ℝ³) (hU : IsOpen U)
    (hinside : ∀ t ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b t ∈ U) :
    ∃ V ∈ nhds b, ∀ z ∈ V, ∀ t ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a z t ∈ U := by
  exact compact_parameter_neighborhood (fun q : ℝ³ × ℝ => shortSphereArc a q.1 q.2)
    b (Set.Icc 0 1) isCompact_Icc U hU
    (shortSphereArc_joint_continuousAt a b ha hb hanti) hinside

lemma greatCirclePoint_ne_neg_center (m t : ℝ³) (hm : ‖m‖ = 1)
    (horth : inner ℝ m t = 0) (a : ℝ) (ha : a ∈ Set.Ioo (-Real.pi) Real.pi) :
    greatCirclePoint m t a ≠ -m := by
  intro heq
  have hinner : inner ℝ m (greatCirclePoint m t a) = Real.cos a := by
    simp [greatCirclePoint, inner_add_right, inner_smul_right, hm, horth]
  rw [heq, inner_neg_right, real_inner_self_eq_norm_sq, hm] at hinner
  have hcos : -1 < Real.cos a := by
    have haabs : |a| < Real.pi := abs_lt.mpr ha
    have h := Real.strictAntiOn_cos
      (show |a| ∈ Set.Icc (0 : ℝ) Real.pi from ⟨abs_nonneg a, haabs.le⟩)
      (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩) haabs
    simpa only [Real.cos_pi, Real.cos_abs] using h
  linarith

/-- The complete perturbation step used to rule out an interior minimizing
great-circle subarc longer than pi: both replacement arcs remain in the given
open region and their total angular length is strictly smaller. -/
theorem great_circle_shortening_inside_open (m t n : ℝ³)
    (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (hn : ‖n‖ = 1)
    (hmt : inner ℝ m t = 0) (hmn : inner ℝ m n = 0) (htn : inner ℝ t n = 0)
    (a : ℝ) (ha : a ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (U : Set ℝ³) (hU : IsOpen U)
    (hleft : ∀ s ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (greatCirclePoint m t (-a)) m s ∈ U)
    (hright : ∀ s ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (greatCirclePoint m t a) m s ∈ U) :
    ∃ z, ‖z‖ = 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (greatCirclePoint m t (-a)) z s ∈ U) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (greatCirclePoint m t a) z s ∈ U) ∧
      sphereAngle (greatCirclePoint m t (-a)) z +
        sphereAngle z (greatCirclePoint m t a) < 2 * a := by
  have hna : -a ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  have hpa : a ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
  obtain ⟨V, hV, hVinside⟩ := shortSphereArc_stable_in_open
    (greatCirclePoint m t (-a)) m (greatCirclePoint_unit m t hm ht hmt (-a)) hm
    (greatCirclePoint_ne_neg_center m t hm hmt (-a) hna) U hU hleft
  obtain ⟨W, hW, hWinside⟩ := shortSphereArc_stable_in_open
    (greatCirclePoint m t a) m (greatCirclePoint_unit m t hm ht hmt a) hm
    (greatCirclePoint_ne_neg_center m t hm hmt a hpa) U hU hright
  obtain ⟨z, hz, hzu, hshort⟩ := arbitrarily_small_great_circle_shortening m t n
    hm ht hn hmt hmn htn a ha (V ∩ W) (Filter.inter_mem hV hW)
  exact ⟨z, hzu, hVinside z hz.1, hWinside z hz.2, hshort⟩

end SquareAntiprismVerification
