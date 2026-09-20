import LeanCode.Monotonic.AnalyticAssembly
import LeanCode.Monotonic.DeformationAnalysis

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

/-- A single admissible configuration has less energy than every square antiprism. -/
theorem verified_counterexample :
    0 < lambda ∧
    StrictlyCompletelyMonotone f ∧
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop ∧
    ∃ Y : Fin 8 → Point, IsConfiguration Y ∧
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ Z : Fin 8 → Point,
        Congruent Z (X a) → Ef f Y < Ef f Z := by
  refine ⟨lambda_pos, f_strictCM lambda_pos, f_tendsto_zero lambda_pos, ?_⟩
  obtain ⟨Y, hY, hE⟩ := deformation_descent f f1 f2 aStar_mem
    (fun _ ht => f_hasDerivAt ht) (fun _ ht => f1_hasDerivAt ht)
    f2_continuous negative_variation
  refine ⟨Y, hY, ?_⟩
  intro a ha Z hZ
  calc
    Ef f Y < G f aStar := hE
    _ ≤ G f a := family_minimum a ha
    _ = Ef f (X a) := (energy_X f ha).symm
    _ = Ef f Z := (energy_congruent f hZ).symm

end SquareAntiprismCounterexample
