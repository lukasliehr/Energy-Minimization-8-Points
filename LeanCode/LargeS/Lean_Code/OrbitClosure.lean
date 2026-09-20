import Lean_Code.SliceCovering

open Real Filter
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def orthogonalOperators : Set (ℝ³ →L[ℝ] ℝ³) := {T | ∀ x, ‖T x‖ = ‖x‖}

lemma orthogonalOperators_isClosed : IsClosed orthogonalOperators := by
  have heq : orthogonalOperators = ⋂ x : ℝ³, {T : ℝ³ →L[ℝ] ℝ³ | ‖T x‖ = ‖x‖} := by
    ext T
    simp [orthogonalOperators]
  rw [heq]
  apply isClosed_iInter
  intro x
  apply isClosed_eq
  · fun_prop
  · exact continuous_const

lemma orthogonalOperators_isCompact : IsCompact orthogonalOperators := by
  apply (isCompact_closedBall (0 : ℝ³ →L[ℝ] ℝ³) 1).of_isClosed_subset orthogonalOperators_isClosed
  intro T hT
  rw [Metric.mem_closedBall, dist_zero_right]
  apply T.opNorm_le_bound (by norm_num)
  intro x
  rw [hT x, one_mul]

def orthogonalOperatorEquiv (T : ℝ³ →L[ℝ] ℝ³) (hT : T ∈ orthogonalOperators) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  let f : ℝ³ →ₗᵢ[ℝ] ℝ³ := { toLinearMap := T.toLinearMap, norm_map' := hT }
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective (f := f.toLinearMap) f.injective)

@[simp] lemma orthogonalOperatorEquiv_apply (T : ℝ³ →L[ℝ] ℝ³)
    (hT : T ∈ orthogonalOperators) (x : ℝ³) : orthogonalOperatorEquiv T hT x = T x := rfl

/-- Compactness of the full congruence orbit, including relabelings, in the
ambient tuple space.  Orthogonal maps are treated as a closed bounded set
of continuous linear operators. -/
theorem congruence_orbit_isCompact (Z : Fin 8 → ℝ³) :
    IsCompact {Y : Fin 8 → ℝ³ | Congruent Z Y} := by
  let orbitPiece (σ : Equiv.Perm (Fin 8)) : Set (Fin 8 → ℝ³) :=
    (fun T : ℝ³ →L[ℝ] ℝ³ => fun i => T (Z (σ i))) '' orthogonalOperators
  have hp : ∀ σ, IsCompact (orbitPiece σ) := by
    intro σ
    exact orthogonalOperators_isCompact.image (by fun_prop)
  have heq : {Y : Fin 8 → ℝ³ | Congruent Z Y} = ⋃ σ, orbitPiece σ := by
    ext Y
    constructor
    · rintro ⟨U, σ, hU⟩
      apply Set.mem_iUnion.mpr
      refine ⟨σ, U.toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
      · intro x
        exact U.norm_map x
      · funext i
        exact (hU i).symm
    · intro hY
      obtain ⟨σ, T, hT, hTY⟩ := Set.mem_iUnion.mp hY
      refine ⟨orthogonalOperatorEquiv T hT, σ, ?_⟩
      intro i
      rw [orthogonalOperatorEquiv_apply]
      exact (congrFun hTY i).symm
  rw [heq]
  exact isCompact_iUnion hp

theorem congruence_orbit_isClosed (Z : Fin 8 → ℝ³) :
    IsClosed {Y : Fin 8 → ℝ³ | Congruent Y Z} := by
  have heq : {Y : Fin 8 → ℝ³ | Congruent Y Z} = {Y : Fin 8 → ℝ³ | Congruent Z Y} := by
    ext Y
    exact ⟨congruent_symm, congruent_symm⟩
  rw [heq]
  exact (congruence_orbit_isCompact Z).isClosed

theorem congruent_of_tendsto (Z Y : Fin 8 → ℝ³) (C : ℕ → (Fin 8 → ℝ³))
    (hC : ∀ n, Congruent (C n) Z) (hlim : Tendsto C atTop (nhds Y)) : Congruent Y Z := by
  exact (congruence_orbit_isClosed Z).mem_of_tendsto hlim (Filter.Eventually.of_forall hC)

theorem congruent_of_arbitrarily_close (Z Y : Fin 8 → ℝ³)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ C : Fin 8 → ℝ³, dist C Y < ε ∧ Congruent C Z) :
    Congruent Y Z := by
  have hclosure : Y ∈ closure {C : Fin 8 → ℝ³ | Congruent C Z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨C, hCdist, hCZ⟩ := hnear ε hε
    exact ⟨C, hCZ, by simpa [dist_comm] using hCdist⟩
  rwa [(congruence_orbit_isClosed Z).closure_eq] at hclosure

end SquareAntiprismVerification
