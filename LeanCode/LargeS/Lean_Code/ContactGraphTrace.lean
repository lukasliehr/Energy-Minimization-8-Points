import Lean_Code.SphericalComplementRegions

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def closedShortSphereArc (a b : ℝ³) : Set ℝ³ :=
  shortSphereArc a b '' Set.Icc (0 : ℝ) 1

lemma closedShortSphereArc_compact (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) : IsCompact (closedShortSphereArc a b) := by
  apply isCompact_Icc.image_of_continuousOn
  intro r hr
  exact (shortSphereArc_continuousAt a b ha hb hanti r hr).continuousWithinAt

lemma contact_endpoints_nonantipodal (a b : ℝ³) (hb : ‖b‖ = 1) (c : ℝ)
    (hc : 0 < c) (hab : inner ℝ a b = c) : a ≠ -b := by
  intro heq
  rw [heq, inner_neg_left, real_inner_self_eq_norm_sq, hb] at hab
  norm_num at hab
  linarith

/-- The embedded graph itself: vertices together with the closed shorter
arcs of all actual contacts. Orienting an edge twice does not change this set. -/
def contactGraphTrace (Y : Fin 8 → ℝ³) (c : ℝ) : Set ℝ³ :=
  Set.range Y ∪ ⋃ d : ContactDart Y c, closedShortSphereArc (Y d.1) (Y d.2.val)

theorem contactGraphTrace_compact (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0 < c) : IsCompact (contactGraphTrace Y c) := by
  classical
  apply Set.Finite.isCompact (Set.finite_range Y) |>.union
  apply isCompact_iUnion
  intro d
  exact closedShortSphereArc_compact _ _ (hY.1 d.1) (hY.1 d.2.val)
    (contact_endpoints_nonantipodal _ _ (hY.1 d.2.val) c hc d.2.property.2)

lemma contactGraphTrace_vertex (Y : Fin 8 → ℝ³) (c : ℝ) (i : Fin 8) :
    Y i ∈ contactGraphTrace Y c := Or.inl ⟨i, rfl⟩

lemma contactGraphTrace_arc (Y : Fin 8 → ℝ³) (c : ℝ) (d : ContactDart Y c)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    shortSphereArc (Y d.1) (Y d.2.val) r ∈ contactGraphTrace Y c :=
  Or.inr (Set.mem_iUnion.mpr ⟨d, r, hr, rfl⟩)

def contactFaceRegion (Y : Fin 8 → ℝ³) (c : ℝ) (a : ℝ³) : Set ℝ³ :=
  closedSphericalComponent (contactGraphTrace Y c)ᶜ a

theorem contactFaceRegion_compact (Y : Fin 8 → ℝ³) (c : ℝ) (a : ℝ³) :
    IsCompact (contactFaceRegion Y c a) := closed_spherical_component_compact _ _

theorem contactFaceRegion_preconnected (Y : Fin 8 → ℝ³) (c : ℝ) (a : ℝ³)
    (ha : ‖a‖ = 1) (haoff : a ∉ contactGraphTrace Y c) :
    IsPreconnected (contactFaceRegion Y c a) := closed_spherical_component_preconnected _ _ ⟨ha, haoff⟩

theorem contactFaceRegion_dense_interior (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0 < c) (a : ℝ³) :
    contactFaceRegion Y c a ⊆ closure (contactFaceRegion Y c a ∩
      sphericalInteriorAmbient (contactFaceRegion Y c a)) :=
  closed_spherical_component_dense_interior _ (contactGraphTrace_compact Y c hY hc).isClosed.isOpen_compl a

theorem contactFaceRegion_model_off_graph (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0 < c) (a x : ℝ³)
    (hx : x ∈ contactFaceRegion Y c a) (hxoff : x ∉ contactGraphTrace Y c) :
    ∃ W : Set ℝ³, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ contactFaceRegion Y c a ↔ ‖y‖ = 1 :=
  closed_spherical_component_model_off_graph _
    (contactGraphTrace_compact Y c hY hc).isClosed.isOpen_compl a x hx hxoff

end SquareAntiprismVerification
