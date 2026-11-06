import ThomsonCompact.Target.Sound
import ThomsonCompact.CoeffMap.Target

/-! # The Riesz `target_link` (for the F0 D16/D18 interface)

With the Riesz normalization `β x = balancedMultiplier c (s x)` (all D16/D18 cells, `c` = cell center), the
retained coordinates of the normalized target are the `targetQ`-combinations of `hfunR c s m j x`, the functions
enclosed by `targetTMsR_sound` (cells: `Target/Cells/Riesz.lean`). This is `CoeffMap.retained_target_sum` (F2) with
that `β`; it is the D16/D18 analogue of `CoeffMap.D12.target_link` (β = 1, `hfun`). -/

namespace ThomsonCompact.Target

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap
open scoped BigOperators

theorem riesz_target_link (c : ℝ) (s : ℝ → ℝ) (D : ℕ) (hD : D ≤ 18) (m : Fin 5 → ℕ) (x : ℝ) (hs : 0 ≤ s x)
    (hm : Profile.Valid D m) (t : RetainedIndex D) :
    retainCompatible (aS (s x)) D
        (normalizedTargetCompatible (s x) (aS (s x)) (balancedMultiplier c (s x)) D m hs (aS_physical _ hs)
          (aS_mem_and_root _ hs).2 hm) t =
      ∑ j : Fin D, (targetQ t.val j : ℝ) * hfunR c s m j x :=
  retained_target_sum (s x) (aS (s x)) (balancedMultiplier c (s x)) D hD m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 hm t

#print axioms riesz_target_link

end ThomsonCompact.Target
