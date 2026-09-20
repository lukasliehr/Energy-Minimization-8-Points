import Lean_Code.CycleSeparationValue

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma solidAngleComplex_continuous (a b : ℝ³) : Continuous (fun p => solidAngleComplex p a b) := by
  have heq (p : ℝ³) : solidAngleComplex p a b =
      (solidAngleDenom p a b : ℂ) + (solidAngleNumer p a b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [solidAngleComplex]
  simp_rw [heq]
  unfold solidAngleDenom solidAngleNumer
  fun_prop

lemma solidAnglePhase_continuousAt (p a b : ℝ³)
    (hslit : solidAngleComplex p a b ∈ Complex.slitPlane) :
    ContinuousAt (fun q => solidAnglePhase q a b) p :=
  continuousAt_const.mul (ContinuousAt.comp (f := fun q => solidAngleComplex q a b)
    (Complex.continuousAt_arg hslit) (solidAngleComplex_continuous a b).continuousAt)

lemma continuousAt_real_finset_sum {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → X → ℝ) (x : X)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) : ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x)
  | @insert i s hi ih =>
    have hh := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert! hh using 1
    funext y
    simp only [Finset.sum_insert hi, Pi.add_apply]

lemma complex_arg_negative_side (z : ℂ) (hr : z.re < 0) (hi : z.im < 0) :
    z.arg = Real.arcsin (-z.im / ‖z‖) - Real.pi := by
  rw [Complex.arg, if_neg (not_le_of_gt hr), if_neg (not_le_of_gt hi), Complex.neg_im]

lemma complex_arg_positive_side (z : ℂ) (hr : z.re < 0) (hi : 0 ≤ z.im) :
    z.arg = Real.arcsin (-z.im / ‖z‖) + Real.pi := by
  rw [Complex.arg, if_neg (not_le_of_gt hr), if_pos hi, Complex.neg_im]

/-- At an edge belonging to the cycle only once, nearby points on opposite
sides have different separation values. The other terms form a continuous
remainder; the one edge term changes by four pi across its branch cut. -/
theorem cycleSeparationValue_edge_separation {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    (i : ι) (p : ℝ³) (hp : ‖p‖ = 1) (hpedge : p ∈ OpenContactArc (v i) (v (σ i)))
    (hother : ∀ j, j ≠ i → p ∉ closedShortSphereArc (v j) (v (σ j))) :
    ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      0 < inner ℝ (crossVec (v i) (v (σ i))) x →
      inner ℝ (crossVec (v i) (v (σ i))) y < 0 →
      cycleSeparationValue σ v x ≠ cycleSeparationValue σ v y := by
  classical
  let Z : ℝ³ → ℂ := fun x => solidAngleComplex (-x) (v i) (v (σ i))
  let R : ℝ³ → ℝ := fun x => ∑ j ∈ Finset.univ.erase i, solidAnglePhase (-x) (v j) (v (σ j))
  let B : ℝ³ → ℝ := fun x => R x + 2 * Real.arcsin (-(Z x).im / ‖Z x‖)
  have hZcont : Continuous Z := (solidAngleComplex_continuous _ _).comp continuous_neg
  have hcut := solidAngleDenom_negative_on_open_arc _ _ p c (hv i) (hv (σ i)) hc (hcontact i) hpedge
  have hZre : (Z p).re < 0 := hcut.1
  have hZne : Z p ≠ 0 := by
    intro heq
    rw [heq] at hZre
    exact lt_irrefl _ hZre
  have hRcont : ContinuousAt R p := by
    apply continuousAt_real_finset_sum
    intro j hj
    have hjne := (Finset.mem_erase.mp hj).1
    have hslit := solidAngleComplex_slit_of_off_arc _ _ p c (hv j) (hv (σ j)) hp hc
      (hcontact j) (hother j hjne)
    exact (solidAnglePhase_continuousAt (-p) _ _ hslit).comp continuous_neg.continuousAt
  have hBcont : ContinuousAt B p := by
    dsimp [B]
    fun_prop (disch := exact norm_ne_zero_iff.mpr hZne)
  have hnear : ∀ᶠ x in nhds p, |B x - B p| < Real.pi := by
    have hh := hBcont (Metric.ball_mem_nhds (B p) Real.pi_pos)
    change ∀ᶠ x in nhds p, dist (B x) (B p) < Real.pi at hh
    simpa only [Real.dist_eq] using hh
  have hnegative : ∀ᶠ x in nhds p, (Z x).re < 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds hZre
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (Filter.inter_mem hnear hnegative)
  have hdecomp (x : ℝ³) : cycleSeparationValue σ v x = R x + 2 * (Z x).arg := by
    exact (Finset.sum_erase_add Finset.univ
      (fun j => solidAnglePhase (-x) (v j) (v (σ j))) (Finset.mem_univ i)).symm
  refine ⟨U, hU, hpU, ?_⟩
  intro x hx y hy hxside hyside heq
  have hxU := hUsub hx
  have hyU := hUsub hy
  change |B x - B p| < Real.pi ∧ (Z x).re < 0 at hxU
  change |B y - B p| < Real.pi ∧ (Z y).re < 0 at hyU
  have hxIm : (Z x).im < 0 := by
    change inner ℝ (crossVec (v i) (v (σ i))) (-x) < 0
    rw [inner_neg_right]
    linarith
  have hyIm : 0 ≤ (Z y).im := by
    change 0 ≤ inner ℝ (crossVec (v i) (v (σ i))) (-y)
    rw [inner_neg_right]
    linarith
  have hxvalue : cycleSeparationValue σ v x = B x - 2 * Real.pi := by
    rw [hdecomp, complex_arg_negative_side (Z x) hxU.2 hxIm]
    dsimp [B]
    ring
  have hyvalue : cycleSeparationValue σ v y = B y + 2 * Real.pi := by
    rw [hdecomp, complex_arg_positive_side (Z y) hyU.2 hyIm]
    dsimp [B]
    ring
  rw [hxvalue, hyvalue] at heq
  have hxb := (abs_lt.mp hxU.1).2
  have hyb := (abs_lt.mp hyU.1).1
  linarith [Real.pi_pos]

/-- The edge jump and constancy along paths together give a genuine
separation statement in the complement of the cycle. -/
theorem cycle_edge_sides_not_joined {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v : ι → ℝ³) (c : ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (v i) (v (σ i)) = c)
    (i : ι) (p : ℝ³) (hp : ‖p‖ = 1) (hpedge : p ∈ OpenContactArc (v i) (v (σ i)))
    (hother : ∀ j, j ≠ i → p ∉ closedShortSphereArc (v j) (v (σ j))) :
    ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      0 < inner ℝ (crossVec (v i) (v (σ i))) x →
      inner ℝ (crossVec (v i) (v (σ i))) y < 0 →
      ¬JoinedIn {z : ℝ³ | ‖z‖ = 1 ∧ z ∉ cycleArcTrace σ v} x y := by
  obtain ⟨U, hU, hpU, hsep⟩ := cycleSeparationValue_edge_separation σ v c hv hc hcontact i p hp hpedge hother
  refine ⟨U, hU, hpU, ?_⟩
  intro x hx y hy hxside hyside hjoined
  exact hsep x hx y hy hxside hyside
    (cycleSeparationValue_joinedIn σ v c hv hc hcontact (fun z hz => hz.1) (fun z hz => hz.2) hjoined)

end SquareAntiprismVerification
