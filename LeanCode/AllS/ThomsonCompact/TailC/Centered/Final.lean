import ThomsonCompact.TailC.Centered.Sound
import ThomsonCompact.TailC.Centered.Row00
import ThomsonCompact.TailC.Centered.Row01
import ThomsonCompact.TailC.Centered.Row10
import ThomsonCompact.TailC.Centered.Row11
import ThomsonCompact.TailC.Centered.Row20
import ThomsonCompact.TailC.Centered.Row21
import ThomsonCompact.TailC.Centered.Row30
import ThomsonCompact.TailC.Centered.Row31
import ThomsonCompact.TailC.Centered.Row40
import ThomsonCompact.TailC.Centered.Row41
import ThomsonCompact.TailC.Centered.Row50
import ThomsonCompact.TailC.Centered.Row51
import ThomsonCompact.TailC.Centered.Row60
import ThomsonCompact.TailC.Centered.Row61
import ThomsonCompact.TailC.Centered.Row70
import ThomsonCompact.TailC.Centered.Row71

/-!
# TailC.Centered: the compact centered quadratic bound (workstream TC1)

`centered_quadratic_bound_four_compact`: the same statement as the old
`Blueprint.Thomson.Tail.Implementation.centered_quadratic_bound_four` (the `hQ` input of
`tail_range_of_tensor_certificates`), from the 16 kernel row leaves `Row*` (exact `ℤ√2[H]` Gram, `Defs`) and the
mirror soundness (`Mirror`, `Sound`); no `N_qentry_*`/`N_qgram_row_*` module is imported.
-/

namespace ThomsonCompact.TailC.Centered
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

theorem rows : ∀ j, rowOk j := by
  rintro ⟨i, b⟩
  fin_cases i <;> fin_cases b
  · exact rowOk_0_0
  · exact rowOk_0_1
  · exact rowOk_1_0
  · exact rowOk_1_1
  · exact rowOk_2_0
  · exact rowOk_2_1
  · exact rowOk_3_0
  · exact rowOk_3_1
  · exact rowOk_4_0
  · exact rowOk_4_1
  · exact rowOk_5_0
  · exact rowOk_5_1
  · exact rowOk_6_0
  · exact rowOk_6_1
  · exact rowOk_7_0
  · exact rowOk_7_1

theorem centered_quadratic_bound_four_compact (q : TangentCoordinates) :
    (∑ e : ContactIndex, contactWeight e * ‖sliceProjection (contactM e q - contactMeanM q)‖ ^ 2) ≤ 4 * ‖q‖ ^ 2 :=
  centered_bound_of_rows rows q

#print axioms centered_quadratic_bound_four_compact

end ThomsonCompact.TailC.Centered
