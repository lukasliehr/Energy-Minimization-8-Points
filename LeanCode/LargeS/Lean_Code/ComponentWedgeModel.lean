import Lean_Code.SphericalWedgePaths

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma mem_closed_of_mem_closure_local (F H W : Set ℝ³) (hH : IsClosed H) (hW : IsOpen W)
    (hsub : F ∩ W ⊆ H) (y : ℝ³) (hy : y ∈ closure F) (hyW : y ∈ W) : y ∈ H := by
  by_contra hyH
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.inter hH.isOpen_compl).mem_nhds ⟨hyW, hyH⟩)
  obtain ⟨z, hzF, hdist⟩ := Metric.mem_closure_iff.mp hy ε hε
  have hz := hball (by simpa only [Metric.mem_ball, dist_comm] using hdist)
  exact hz.2 (hsub ⟨hzF, hz.1⟩)

lemma mem_closure_cap_strict_normals {ι : Type*} [Nonempty ι] (normal : ι → ℝ³)
    (p d y : ℝ³) (δ : ℝ) (hy : y ∈ sphericalOpenCap p δ)
    (hyN : ∀ i, 0 ≤ inner ℝ (normal i) y) (hdN : ∀ i, 0 < inner ℝ (normal i) d) :
    y ∈ closure {x : ℝ³ | x ∈ sphericalOpenCap p δ ∧ ∀ i, 0 < inner ℝ (normal i) x} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let U := Metric.ball y ε ∩ {x : ℝ³ | δ < inner ℝ p x}
  have hU : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hyU : y ∈ U := ⟨Metric.mem_ball_self hε, hy.2⟩
  obtain ⟨x, hxU, hxu, hxN⟩ := unit_nearby_nonnegative_normals normal y d hy.1 hyN hdN U hU hyU
  exact ⟨x, ⟨⟨hxu, hxU.2⟩, hxN⟩, by simpa only [Metric.mem_ball, dist_comm] using hxU.1⟩

/-- Once a component meets the interior of a locally empty wedge and is
separated from its exterior, its closure has the exact closed-wedge model.
No global boundary parametrization or disk theorem is assumed. -/
theorem component_wedge_local_model (U : Set ℝ³) (a p n₁ n₂ d : ℝ³)
    (δ : ℝ) (hδ : 0 < δ)
    (hd₁ : 0 < inner ℝ n₁ d) (hd₂ : 0 < inner ℝ n₂ d)
    (hinside : ∀ y ∈ sphericalOpenCap p δ,
      0 < inner ℝ n₁ y → 0 < inner ℝ n₂ y → y ∈ U)
    (x : ℝ³) (hx : x ∈ pathComponentIn (openSphericalRegion U) a)
    (hxcap : x ∈ sphericalOpenCap p δ) (hx₁ : 0 < inner ℝ n₁ x) (hx₂ : 0 < inner ℝ n₂ x)
    (hsep : ∀ y ∈ sphericalOpenCap p δ,
      (inner ℝ n₁ y < 0 ∨ inner ℝ n₂ y < 0) → ¬JoinedIn (openSphericalRegion U) x y) :
    ∀ y : ℝ³, δ < inner ℝ p y →
      (y ∈ closedSphericalComponent U a ↔
        ‖y‖ = 1 ∧ 0 ≤ inner ℝ n₁ y ∧ 0 ≤ inner ℝ n₂ y) := by
  let F := pathComponentIn (openSphericalRegion U) a
  let W : Set ℝ³ := {y | δ < inner ℝ p y}
  let H : Set ℝ³ := {y | ‖y‖ = 1 ∧ 0 ≤ inner ℝ n₁ y ∧ 0 ≤ inner ℝ n₂ y}
  have hW : IsOpen W := isOpen_lt continuous_const (by fun_prop)
  have hH : IsClosed H := by
    have hn : IsClosed {y : ℝ³ | ‖y‖ = 1} := isClosed_eq continuous_norm continuous_const
    have hn₁ : IsClosed {y : ℝ³ | 0 ≤ inner ℝ n₁ y} := isClosed_le continuous_const (by fun_prop)
    have hn₂ : IsClosed {y : ℝ³ | 0 ≤ inner ℝ n₂ y} := isClosed_le continuous_const (by fun_prop)
    exact hn.inter (hn₁.inter hn₂)
  have hsub : F ∩ W ⊆ H := by
    intro y hy
    have hyu := (pathComponentIn_subset hy.1).1
    have hxy : JoinedIn (openSphericalRegion U) x y := hx.symm.trans hy.1
    refine ⟨hyu, le_of_not_gt ?_, le_of_not_gt ?_⟩
    · intro hneg
      exact hsep y ⟨hyu, hy.2⟩ (Or.inl hneg) hxy
    · intro hneg
      exact hsep y ⟨hyu, hy.2⟩ (Or.inr hneg) hxy
  let normal : Bool → ℝ³ := fun i => if i then n₁ else n₂
  let I : Set ℝ³ := {y | y ∈ sphericalOpenCap p δ ∧ ∀ i, 0 < inner ℝ (normal i) y}
  have hIF : I ⊆ F := by
    intro y hy
    have hy₁ : 0 < inner ℝ n₁ y := hy.2 true
    have hy₂ : 0 < inner ℝ n₂ y := hy.2 false
    have hin (z : ℝ³) (hz : z ∈ sphericalOpenCap p δ)
        (hz₁ : 0 < inner ℝ n₁ z) (hz₂ : 0 < inner ℝ n₂ z) : z ∈ openSphericalRegion U :=
      ⟨hz.1, hinside z hz hz₁ hz₂⟩
    exact hx.trans (joinedIn_cap_wedge_interior p n₁ n₂ δ hδ _ hin x y hxcap hy.1 hx₁ hx₂ hy₁ hy₂)
  intro y hycap
  constructor
  · intro hyD
    exact mem_closed_of_mem_closure_local F H W hH hW hsub y hyD hycap
  · intro hyH
    have hyN : ∀ i, 0 ≤ inner ℝ (normal i) y := by
      intro i; cases i <;> simp [normal, hyH.2.1, hyH.2.2]
    have hdN : ∀ i, 0 < inner ℝ (normal i) d := by
      intro i; cases i <;> simp [normal, hd₁, hd₂]
    exact closure_mono hIF (mem_closure_cap_strict_normals normal p d y δ ⟨hyH.1, hycap⟩ hyN hdN)

end SquareAntiprismVerification
