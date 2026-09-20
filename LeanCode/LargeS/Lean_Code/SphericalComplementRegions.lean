import Lean_Code.LocalToGlobalArcConvexity

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def shortSpherePath (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hanti : a ≠ -b) : Path a b where
  toFun r := shortSphereArc a b r.val
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (shortSphereArc_continuousAt a b ha hb hanti r.val r.property).comp
      continuous_subtype_val.continuousAt
  source' := shortSphereArc_zero a b ha
  target' := shortSphereArc_one a b hb

lemma joinedIn_of_short_arc {D : Set ℝ³} (a b : ℝ³)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hanti : a ≠ -b)
    (hinside : ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b r ∈ D) : JoinedIn D a b :=
  ⟨shortSpherePath a b ha hb hanti, fun r => hinside r.val r.property⟩

def openSphericalRegion (U : Set ℝ³) : Set ℝ³ := {x | ‖x‖ = 1 ∧ x ∈ U}

/-- Faces are defined as actual path components of the spherical complement,
and their closed regions are actual closures. No convexity is built into
these definitions. -/
def closedSphericalComponent (U : Set ℝ³) (a : ℝ³) : Set ℝ³ :=
  closure (pathComponentIn (openSphericalRegion U) a)

lemma open_spherical_component_local (U : Set ℝ³) (hU : IsOpen U)
    (a x : ℝ³) (hx : x ∈ pathComponentIn (openSphericalRegion U) a) :
    ∃ W : Set ℝ³, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ‖y‖ = 1 → y ∈ pathComponentIn (openSphericalRegion U) a := by
  have hxA : x ∈ openSphericalRegion U := pathComponentIn_subset hx
  have hxunit := hxA.1
  have hanti : x ≠ -x := by
    intro heq
    have hh := congrArg (fun y => inner ℝ x y) heq
    simp [inner_neg_right, real_inner_self_eq_norm_sq, hxunit] at hh
    norm_num at hh
  obtain ⟨V, hV, hinside⟩ := shortSphereArc_stable_in_open x x hxunit hxunit hanti U hU (by
    intro r hr
    simpa only [shortSphereArc_self_unit x hxunit r] using hxA.2)
  have hne : {y : ℝ³ | x ≠ -y} ∈ nhds x :=
    (isOpen_ne_fun continuous_const (continuous_neg)).mem_nhds hanti
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp (Filter.inter_mem hV hne)
  refine ⟨W, hWopen, hxW, ?_⟩
  intro y hy hyunit
  have hyV := hWsub hy
  have hxy : JoinedIn (openSphericalRegion U) x y :=
    joinedIn_of_short_arc x y hxunit hyunit hyV.2 (by
      intro r hr
      exact ⟨shortSphereArc_unit x y hxunit hyunit hyV.2 r hr, hinside y hyV.1 r hr⟩)
  exact hx.trans hxy

lemma closed_spherical_component_unit (U : Set ℝ³) (a : ℝ³) :
    ∀ x ∈ closedSphericalComponent U a, ‖x‖ = 1 := by
  have hclosed : IsClosed {x : ℝ³ | ‖x‖ = 1} := isClosed_eq continuous_norm continuous_const
  apply closure_minimal _ hclosed
  intro x hx
  exact (pathComponentIn_subset hx).1

lemma closed_spherical_component_preconnected (U : Set ℝ³) (a : ℝ³)
    (ha : a ∈ openSphericalRegion U) : IsPreconnected (closedSphericalComponent U a) :=
  (isPathConnected_pathComponentIn ha).isConnected.isPreconnected.closure

lemma closed_spherical_component_compact (U : Set ℝ³) (a : ℝ³) :
    IsCompact (closedSphericalComponent U a) :=
  spherePoint_isCompact.of_isClosed_subset isClosed_closure
    (closed_spherical_component_unit U a)

/-- Relative interior density of a face closure is proved from local access
in the open spherical complement, independently of boundary simplicity. -/
lemma closed_spherical_component_dense_interior (U : Set ℝ³) (hU : IsOpen U) (a : ℝ³) :
    closedSphericalComponent U a ⊆
      closure (closedSphericalComponent U a ∩ sphericalInteriorAmbient (closedSphericalComponent U a)) := by
  apply closure_mono
  intro x hx
  refine ⟨subset_closure hx, ?_⟩
  obtain ⟨W, hW, hxW, hWcomp⟩ := open_spherical_component_local U hU a x hx
  exact mem_sphericalInteriorAmbient_of_open hW
    (fun y hy hu => subset_closure (hWcomp y hy hu)) hxW

/-- Taking the closure adds no new points away from the excluded graph:
path components are relatively open and relatively closed in the open
spherical region. -/
lemma closed_spherical_component_mem_of_open (U : Set ℝ³) (hU : IsOpen U)
    (a x : ℝ³) (hx : x ∈ closedSphericalComponent U a) (hxU : x ∈ U) :
    x ∈ pathComponentIn (openSphericalRegion U) a := by
  have hxunit := closed_spherical_component_unit U a x hx
  have hxA : x ∈ openSphericalRegion U := ⟨hxunit, hxU⟩
  obtain ⟨W, hW, hxW, hWcomp⟩ := open_spherical_component_local U hU x x
    (mem_pathComponentIn_self hxA)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hxW)
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  have hyW : y ∈ W := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  have hyunit := (pathComponentIn_subset hy).1
  have hxy : JoinedIn (openSphericalRegion U) x y := hWcomp y hyW hyunit
  exact hy.trans hxy.symm

/-- Off the graph, the actual closed face has the zero-halfspace local
model: a full neighborhood on the unit sphere. -/
theorem closed_spherical_component_model_off_graph (U : Set ℝ³) (hU : IsOpen U)
    (a x : ℝ³) (hx : x ∈ closedSphericalComponent U a) (hxU : x ∈ U) :
    ∃ W : Set ℝ³, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ closedSphericalComponent U a ↔ ‖y‖ = 1 := by
  have hxcomp := closed_spherical_component_mem_of_open U hU a x hx hxU
  obtain ⟨W, hW, hxW, hWcomp⟩ := open_spherical_component_local U hU a x hxcomp
  exact ⟨W, hW, hxW, fun y hy =>
    ⟨closed_spherical_component_unit U a y, fun hu => subset_closure (hWcomp y hy hu)⟩⟩

end SquareAntiprismVerification
