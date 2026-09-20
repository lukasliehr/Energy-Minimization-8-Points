import Lean_Code.GreatCircleInteriorPropagation

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma shortSphereArc_self_unit (a : ℝ³) (ha : ‖a‖ = 1) (r : ℝ) : shortSphereArc a a r = a := by
  have hc : (1 - r) • a + r • a = a := by module
  unfold shortSphereArc
  rw [hc]
  simp [sphereNormalize, ha]

/-- An interior point and any nonantipodal point of a compact, connected,
locally polyhedral spherical region are joined by their shorter arc in the
region. No global convexity or hemispherical assumption is made. -/
theorem short_arc_from_interior {D : Set ℝ³} [PreconnectedSpace D]
    (P : CompactArcPatchCover D) (hmodel : LocallySphericalPolyhedral D)
    (a b : ℝ³) (haD : a ∈ D) (hbD : b ∈ D)
    (haI : a ∈ sphericalInteriorAmbient D) (hanti : a ≠ -b) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b r ∈ D := by
  have ha := hmodel.unit a haD
  have hb := hmodel.unit b hbD
  by_cases hab : a = b
  · subst b
    intro r hr
    simpa only [shortSphereArc_self_unit a ha r] using haD
  have hne : (⟨a, haD⟩ : D) ≠ ⟨b, hbD⟩ := fun h => hab (congrArg Subtype.val h)
  obtain ⟨p, t, ht, hat, hmin, hpos, hend, htrace⟩ :=
    minimizing_great_circle_trace_exists P hmodel.unit ⟨a, haD⟩ ⟨b, hbD⟩ hne
  have hle := shortest_great_circle_length_le_pi_of_interior_start P hmodel p hmin
    t ha ht hat hend htrace haI
  have hlt : p.length < Real.pi := by
    by_contra hn
    have heq : p.length = Real.pi := le_antisymm hle (le_of_not_gt hn)
    have hbneg : -a = b := by simpa [heq, greatCirclePoint] using hend
    exact hanti (by rw [← hbneg, neg_neg])
  intro r hr
  obtain ⟨u, hu, heq⟩ := shortSphereArc_greatCircle_parameter a t ha ht hat
    p.length ⟨hpos, hlt⟩ r hr
  rw [hend] at heq
  rw [heq]
  exact htrace u hu

lemma shortSphereArc_left_continuousAt (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun x => shortSphereArc x b r) a := by
  have hcomb : ContinuousAt (fun x : ℝ³ => (1 - r) • x + r • b) a := by fun_prop
  exact ContinuousAt.comp (f := fun x : ℝ³ => (1 - r) • x + r • b)
    (sphereNormalize_continuousAt _ (shortSphereArc_combination_ne_zero a b ha hb hanti r hr)) hcomb

/-- Closedness extends shorter-arc containment from interior start points
to all start points when the relative interior is dense in the region. -/
theorem shortArcClosed_of_dense_interior {D : Set ℝ³} [PreconnectedSpace D]
    (P : CompactArcPatchCover D) (hmodel : LocallySphericalPolyhedral D) (hclosed : IsClosed D)
    (hdense : D ⊆ closure (D ∩ sphericalInteriorAmbient D)) : ShortArcClosed D := by
  intro a haD b hbD hanti r hr
  by_contra hnot
  have hcont := shortSphereArc_left_continuousAt a b (hmodel.unit a haD) (hmodel.unit b hbD) hanti r hr
  have hbad : ∀ᶠ x in nhds a, shortSphereArc x b r ∉ D :=
    hcont (hclosed.isOpen_compl.mem_nhds hnot)
  have hantiE : ∀ᶠ x in nhds a, x ≠ -b :=
    (isOpen_ne_fun continuous_id continuous_const).mem_nhds hanti
  have hevent : {x | shortSphereArc x b r ∉ D ∧ x ≠ -b} ∈ nhds a :=
    Filter.inter_mem hbad hantiE
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp (hdense haD) ε hε
  have hxball : x ∈ Metric.ball a ε := by
    simpa only [Metric.mem_ball, dist_comm] using hdist
  obtain ⟨hxbad, hxanti⟩ := hball hxball
  exact hxbad (short_arc_from_interior P hmodel x b hx.1 hbD hx.2 hxanti r hr)

/-- The compact local models and density hypotheses suffice for global
shorter-arc convexity. The finite patch cover is constructed, not assumed. -/
theorem shortArcClosed_of_compact_local_models {D : Set ℝ³} [PreconnectedSpace D]
    (hcompact : IsCompact D) (hmodel : LocallySphericalPolyhedral D)
    (hdense : D ⊆ closure (D ∩ sphericalInteriorAmbient D)) : ShortArcClosed D := by
  obtain ⟨P⟩ := compact_arc_cover_of_local_models hcompact hmodel
  exact shortArcClosed_of_dense_interior P hmodel hcompact.isClosed hdense

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

/-- The actual-face application now needs only the topological region and
its local geometry. Global convexity, global support, and hemisphere
containment are conclusions of the checked argument, not hypotheses. -/
theorem strict_support_of_local_face_region (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (D : Set ℝ³) [PreconnectedSpace D] (hcompact : IsCompact D)
    (hmodel : LocallySphericalPolyhedral D)
    (hdense : D ⊆ closure (D ∩ sphericalInteriorAmbient D))
    (hvertices : ∀ i, Y (C.vertex i) ∈ D)
    (hedges : ∀ i, ∃ z ∈ D,
      inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) z = 0 ∧
      ∃ ε > 0, ∀ x ∈ D, dist x z < ε →
        0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) x) : C.StrictSupport :=
  C.strict_support_of_short_arc_region hirr hbound D hmodel.unit
    (shortArcClosed_of_compact_local_models hcompact hmodel hdense) hvertices hedges

end ContactBoundaryCycle
end SquareAntiprismVerification
