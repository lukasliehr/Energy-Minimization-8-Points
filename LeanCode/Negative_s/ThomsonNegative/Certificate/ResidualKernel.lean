import ThomsonNegative.Certificate.CoefficientKernel
import ThomsonNegative.Certificate.TargetData

/-! The complete 68-coordinate residual, retaining every enclosure error. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

def targetRowTM (c : Ctx) (H : List TM) (r : Nat) : TM :=
  let t := TargetData.entry r
  cond (Nat.beq t.2.2 0) zeroTM
    (rationalScale c t.2.1 t.2.2 3 (H.getD t.1 zeroTM))

def residualRowTM (c : Ctx) (images : List (List TM)) (H : List TM) (r : Nat) : TM :=
  let image := refresh c (sumTM c (fun b => (images.getD b []).getD r zeroTM) 8)
  refresh c (add c (targetRowTM c H r) (neg c image))

def residualTM (c : Ctx) (images : List (List TM)) (H : List TM) : List TM :=
  (List.range 68).map (residualRowTM c images H)

end ThomsonNegative.Certificate
