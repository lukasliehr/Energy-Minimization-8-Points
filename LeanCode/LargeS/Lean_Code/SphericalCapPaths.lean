import Lean_Code.ContactEndpointGeometry

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sphericalOpenCap (p : ℝ³) (δ : ℝ) : Set ℝ³ :=
  {x | ‖x‖ = 1 ∧ δ < inner ℝ p x}

lemma sphericalOpenCap_small (p : ℝ³) (hp : ‖p‖ = 1)
    (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1, sphericalOpenCap p δ ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  let ρ : ℝ := min ε 1 / 2
  have hρ : 0 < ρ := half_pos (lt_min hε zero_lt_one)
  have hρε : ρ < ε := by dsimp [ρ]; have := min_le_left ε 1; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := min_le_right ε 1; linarith
  let δ : ℝ := 1 - ρ ^ 2 / 2
  have hδ0 : 0 < δ := by dsimp [δ]; nlinarith
  have hδ1 : δ < 1 := by dsimp [δ]; nlinarith [sq_pos_of_pos hρ]
  refine ⟨δ, ⟨hδ0, hδ1⟩, ?_⟩
  intro y hy
  have hsq : dist y p ^ 2 = 2 - 2 * inner ℝ p y := by
    rw [dist_eq_norm, norm_sub_sq_real, hy.1, hp, real_inner_comm p y]
    ring
  have hcap := hy.2
  change 1 - ρ ^ 2 / 2 < inner ℝ p y at hcap
  apply hball
  change dist y p < ε
  nlinarith [dist_nonneg (x := y) (y := p),
    mul_pos (sub_pos.mpr hρε) (show 0 < ε + ρ by linarith)]

lemma sphericalOpenCap_nonantipodal (p : ℝ³) (δ : ℝ) (hδ : 0 < δ)
    {a b : ℝ³} (ha : a ∈ sphericalOpenCap p δ) (hb : b ∈ sphericalOpenCap p δ) : a ≠ -b := by
  intro heq
  have hpa := ha.2
  have hpb := hb.2
  rw [heq, inner_neg_right] at hpa
  linarith

lemma sphericalOpenCap_arcClosed (p : ℝ³) (δ : ℝ) (hδ : 0 < δ) :
    ShortArcClosed (sphericalOpenCap p δ) := by
  intro a ha b hb hanti r hr
  let d := min (inner ℝ p a) (inner ℝ p b)
  have hd : δ < d := lt_min ha.2 hb.2
  let normal : Fin 0 → ℝ³ := Fin.elim0
  have ha' : a ∈ sphericalHalfspacePatch normal p d :=
    ⟨ha.1, min_le_left _ _, fun i => Fin.elim0 i⟩
  have hb' : b ∈ sphericalHalfspacePatch normal p d :=
    ⟨hb.1, min_le_right _ _, fun i => Fin.elim0 i⟩
  have hh := sphericalHalfspacePatch_arcClosed normal p d (hδ.trans hd) a ha' b hb' hanti r hr
  exact ⟨hh.1, hd.trans_le hh.2.1⟩

lemma shortSphereArc_inner_pos (n a b : ℝ³) (r : ℝ)
    (ha : 0 < inner ℝ n a) (hb : 0 < inner ℝ n b) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 < inner ℝ n (shortSphereArc a b r) :=
  sphereNormalize_inner_pos n _ (positive_segment_inner n a b r ha hb hr)

/-- Strict linear inequalities are preserved by shorter arcs in a small
spherical cap, so their intersection is path-connected. -/
lemma joinedIn_cap_strict_halfspaces {ι : Type*} (normal : ι → ℝ³)
    (p : ℝ³) (δ : ℝ) (hδ : 0 < δ) (D : Set ℝ³)
    (hin : ∀ x ∈ sphericalOpenCap p δ, (∀ i, 0 < inner ℝ (normal i) x) → x ∈ D)
    (a b : ℝ³) (ha : a ∈ sphericalOpenCap p δ) (hb : b ∈ sphericalOpenCap p δ)
    (haN : ∀ i, 0 < inner ℝ (normal i) a) (hbN : ∀ i, 0 < inner ℝ (normal i) b) :
    JoinedIn D a b := by
  have hanti := sphericalOpenCap_nonantipodal p δ hδ ha hb
  apply joinedIn_of_short_arc a b ha.1 hb.1 hanti
  intro r hr
  exact hin _ (sphericalOpenCap_arcClosed p δ hδ a ha b hb hanti r hr)
    (fun i => shortSphereArc_inner_pos (normal i) a b r (haN i) (hbN i) hr)

/-- A tangent direction satisfying finitely many strict inequalities gives
unit points satisfying the same inequalities arbitrarily close to the base.
The index type need not be finite, but is nonempty to guarantee nonzero
normalization from one of the strict inequalities. -/
lemma unit_nearby_nonnegative_normals {ι : Type*} [Nonempty ι] (normal : ι → ℝ³)
    (p d : ℝ³) (hp : ‖p‖ = 1)
    (hpN : ∀ i, 0 ≤ inner ℝ (normal i) p) (hdN : ∀ i, 0 < inner ℝ (normal i) d)
    (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ x ∈ U, ‖x‖ = 1 ∧ ∀ i, 0 < inner ℝ (normal i) x := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  let f : ℝ → ℝ³ := fun s => sphereNormalize (p + s • d)
  have hf : ContinuousAt f 0 := by
    apply ContinuousAt.comp (f := fun s : ℝ => p + s • d)
      (sphereNormalize_continuousAt _ (by simpa using hpne))
    fun_prop
  have hf0 : f 0 = p := by simp [f, sphereNormalize, hp]
  have hnear : {s | f s ∈ U} ∈ nhds (0 : ℝ) :=
    hf (by simpa only [hf0] using hU.mem_nhds hpU)
  obtain ⟨s, hsU, hs0, hs1⟩ := exists_small_positive_in_neighborhood _ hnear 1 zero_lt_one
  have hpos (i : ι) : 0 < inner ℝ (normal i) (p + s • d) := by
    simp only [inner_add_right, inner_smul_right]
    exact add_pos_of_nonneg_of_pos (hpN i) (mul_pos hs0 (hdN i))
  let i : ι := Classical.choice ‹Nonempty ι›
  refine ⟨f s, hsU, sphereNormalize_unit _ (inner_pos_ne_zero (normal i) _ (hpos i)), ?_⟩
  intro j
  exact sphereNormalize_inner_pos _ _ (hpos j)

lemma unit_nearby_strict_normals {ι : Type*} [Nonempty ι] (normal : ι → ℝ³)
    (p d : ℝ³) (hp : ‖p‖ = 1)
    (hpN : ∀ i, inner ℝ (normal i) p = 0) (hdN : ∀ i, 0 < inner ℝ (normal i) d)
    (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ x ∈ U, ‖x‖ = 1 ∧ ∀ i, 0 < inner ℝ (normal i) x :=
  unit_nearby_nonnegative_normals normal p d hp (fun i => (hpN i).ge) hdN U hU hpU

lemma unit_both_sides_in_open (p n : ℝ³) (hp : ‖p‖ = 1) (hn : n ≠ 0)
    (hplane : inner ℝ n p = 0) (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ x ∈ U, ∃ y ∈ U, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      0 < inner ℝ n x ∧ inner ℝ n y < 0 := by
  have hnn : 0 < inner ℝ n n := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hn)
  obtain ⟨x, hx, hxu, hxN⟩ := unit_nearby_strict_normals (fun _ : Unit => n) p n hp
    (fun _ => hplane) (fun _ => hnn) U hU hpU
  obtain ⟨y, hy, hyu, hyN⟩ := unit_nearby_strict_normals (fun _ : Unit => -n) p (-n) hp
    (fun _ => by simp [hplane]) (fun _ => by simpa using hnn) U hU hpU
  refine ⟨x, hx, y, hy, hxu, hyu, hxN (), ?_⟩
  have hh := hyN ()
  simp only [inner_neg_left] at hh
  linarith

end SquareAntiprismVerification
