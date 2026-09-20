import Lean_Code.SolidAngleDomain

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def cycleArcTrace {ι : Type*} (σ : Equiv.Perm ι) (v : ι → ℝ³) : Set ℝ³ :=
  ⋃ i, closedShortSphereArc (v i) (v (σ i))

def cycleSeparationValue {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (v : ι → ℝ³) (x : ℝ³) : ℝ :=
  ∑ i, solidAnglePhase (-x) (v i) (v (σ i))

theorem cycleArcTrace_compact {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (v : ι → ℝ³)
    (c : ℝ) (hv : ∀ i, ‖v i‖ = 1) (hc : 0 < c) (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c) :
    IsCompact (cycleArcTrace σ v) := by
  apply isCompact_iUnion
  intro i
  exact closedShortSphereArc_compact _ _ (hv i) (hv (σ i))
    (contact_endpoints_nonantipodal _ _ (hv (σ i)) c hc (hcontact i))

/-- The endpoint terms cancel exactly around any finite permutation cycle. -/
theorem cycleSeparationValue_curve_derivative {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    {f : ℝ → ℝ³} {h : ℝ³} {r : ℝ} (hf : HasDerivAt f h r)
    (hu : ‖f r‖ = 1) (horth : inner ℝ (f r) h = 0) (hoff : f r ∉ cycleArcTrace σ v) :
    HasDerivAt (fun s => cycleSeparationValue σ v (f s)) 0 r := by
  classical
  let g : ι → ℝ := fun i => inner ℝ (crossVec (-(f r)) (v i)) (-h) / (1 + inner ℝ (-(f r)) (v i))
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun s => solidAnglePhase (-(f s)) (v i) (v (σ i))) (g (σ i) - g i) r := by
    intro i hi
    apply solidAnglePhase_curve_derivative hf.neg _ _ (by simpa using hu) (hv i) (hv (σ i))
      (by simpa using horth)
    apply solidAngleComplex_slit_of_off_arc _ _ _ c (hv i) (hv (σ i)) hu hc (hcontact i)
    intro hin
    exact hoff (Set.mem_iUnion.mpr ⟨i, hin⟩)
  have hsum := HasDerivAt.sum hterm
  have hcancel : (∑ i, (g (σ i) - g i)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp σ]
    exact sub_self _
  rw [hcancel] at hsum
  convert! hsum using 1
  funext s
  simp only [cycleSeparationValue, Finset.sum_apply]

lemma greatCirclePoint_hasDerivAt (m t : ℝ³) (s : ℝ) :
    HasDerivAt (greatCirclePoint m t) (greatCircleTangent m t s) s := by
  have h := ((Real.hasDerivAt_cos s).smul_const m).add ((Real.hasDerivAt_sin s).smul_const t)
  exact h

lemma eq_endpoints_of_hasDerivAt_zero (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hder : ∀ r ∈ Set.Icc (0 : ℝ) L, HasDerivAt f 0 r) : f 0 = f L := by
  apply (convex_Icc (0 : ℝ) L).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
  · intro r hr
    exact (hder r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    have hd : HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) r := by simpa using (hder r hr).hasFDerivAt
    exact hd.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hL r hr)
  · exact ⟨le_rfl, hL.le⟩
  · exact ⟨hL.le, le_rfl⟩

/-- Constancy on a great-circle interval that does not meet the cycle. -/
theorem cycleSeparationValue_great_circle_constant {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (L : ℝ) (hL : 0 < L)
    (hoff : ∀ r ∈ Set.Icc (0 : ℝ) L, greatCirclePoint m t r ∉ cycleArcTrace σ v) :
    cycleSeparationValue σ v m = cycleSeparationValue σ v (greatCirclePoint m t L) := by
  have h := eq_endpoints_of_hasDerivAt_zero (fun r => cycleSeparationValue σ v (greatCirclePoint m t r))
    L hL (by
      intro r hr
      exact cycleSeparationValue_curve_derivative σ v c hv hc hcontact (greatCirclePoint_hasDerivAt m t r)
        (greatCirclePoint_unit m t hm ht horth r) (greatCircleTangent_orthogonal m t hm ht horth r) (hoff r hr))
  simpa only [greatCirclePoint_zero] using h

/-- The angle sum is locally constant on the spherical complement of the
cycle. The neighborhood is constructed by uniform stability of short arcs. -/
theorem cycleSeparationValue_locally_constant {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    (x : ℝ³) (hx : ‖x‖ = 1) (hxoff : x ∉ cycleArcTrace σ v) :
    ∃ W : Set ℝ³, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, ‖y‖ = 1 →
      cycleSeparationValue σ v y = cycleSeparationValue σ v x := by
  have hU := (cycleArcTrace_compact σ v c hv hc.1 hcontact).isClosed.isOpen_compl
  have hanti : x ≠ -x := by
    intro heq
    have hh := congrArg (fun y => inner ℝ x y) heq
    simp [inner_neg_right, hx] at hh
    norm_num at hh
  obtain ⟨V, hV, hinside⟩ := shortSphereArc_stable_in_open x x hx hx hanti
    (cycleArcTrace σ v)ᶜ hU (by
      intro r hr
      change shortSphereArc x x r ∉ cycleArcTrace σ v
      rw [shortSphereArc_self_unit x hx r]
      exact hxoff)
  have hne : {y : ℝ³ | x ≠ -y} ∈ nhds x :=
    (isOpen_ne_fun continuous_const continuous_neg).mem_nhds hanti
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp (Filter.inter_mem hV hne)
  refine ⟨W, hW, hxW, ?_⟩
  intro y hy hyunit
  by_cases hxy : x = y
  · rw [hxy]
  have hyV := hWsub hy
  obtain ⟨t, ht, hxt, hframe⟩ := short_arc_frame_exists x y hx hyunit hxy hyV.2
  have hθ : sphereAngle x y ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨sphereAngle_pos_of_ne x y hx hyunit hxy,
      sphereAngle_lt_pi_of_nonantipodal x y hx hyunit hyV.2⟩
  have htrace : ∀ u ∈ Set.Icc (0 : ℝ) (sphereAngle x y),
      greatCirclePoint x t u ∉ cycleArcTrace σ v := by
    intro u hu
    obtain ⟨hr, heq⟩ := greatCirclePoint_shortArc_parameter x t hx ht hxt (sphereAngle x y) hθ u hu
    rw [hframe] at heq
    rw [← heq]
    exact hinside y hyV.1 _ hr
  have hh := cycleSeparationValue_great_circle_constant σ v c hv hc hcontact
    x t hx ht hxt (sphereAngle x y) hθ.1 htrace
  rw [hframe] at hh
  exact hh.symm

/-- The separation value is constant along every genuine continuous path
avoiding the cycle, not just along the auxiliary geodesic patch chains. -/
theorem cycleSeparationValue_joinedIn {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    {D : Set ℝ³} (hunit : ∀ x ∈ D, ‖x‖ = 1)
    (hoff : ∀ x ∈ D, x ∉ cycleArcTrace σ v) {a b : ℝ³} (hab : JoinedIn D a b) :
    cycleSeparationValue σ v a = cycleSeparationValue σ v b := by
  obtain ⟨γ, hγ⟩ := hab
  let R : unitInterval → ℝ := fun r => cycleSeparationValue σ v (γ r)
  have hlocal : ∀ r : unitInterval, ∀ᶠ s in nhds r, R r = R s := by
    intro r
    obtain ⟨W, hW, hrW, hvalue⟩ := cycleSeparationValue_locally_constant σ v c hv hc hcontact
      (γ r) (hunit _ (hγ r)) (hoff _ (hγ r))
    have hevent : ∀ᶠ s in nhds r, γ s ∈ W := γ.continuous.continuousAt (hW.mem_nhds hrW)
    filter_upwards [hevent] with s hs
    exact (hvalue (γ s) hs (hunit _ (hγ s))).symm
  have hchain := reflTransGen_of_local_relation (fun r s : unitInterval => R r = R s)
    (fun r s h => h.symm) hlocal 0 1
  have hrel : ∀ r s, Relation.ReflTransGen (fun u w : unitInterval => R u = R w) r s → R r = R s := by
    intro r s hs
    induction hs with
    | refl => rfl
    | tail hpath hstep ih => exact ih.trans hstep
  have heq : R 0 = R 1 := hrel 0 1 hchain
  simpa only [R, γ.source, γ.target] using heq

end SquareAntiprismVerification
