import ThomsonNegative.Certificate.Correction.q03.Input
import ThomsonNegative.Certificate.Correction.InputSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q03
set_option maxRecDepth 100000
open ThomsonNegative.Compact.Packed

/-- The actual extended root is used on the original cell parameter, even
though the correction arithmetic itself has Taylor order zero. -/
theorem argument_encl : Encl context argument
    (fun t => Compact.Target.ScalarCells.heightFunction (1:Fin 5) t-83/256) := by
  have he := sameTM_eq argument_checked
  have haok : argumentComputed.ok=true := by
    have hh := argument_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hheight := Compact.Target.ScalarCells.height_encl (1:Fin 5)
  change Encl sourceContext Compact.Target.Cells.Q03.data.heightCheckpoint
    (Compact.Target.ScalarCells.heightFunction (1:Fin 5)) at hheight
  have hs := buildArgument_sound hheight 0x533b99e600d417fac9a3df106b7adbaeb2bbbd19dcb9c3b5c216ded03e241192e4ce4e4a80cfc67b3cd9cb4ed78f58c0 haok
  change Encl context argumentComputed _ at hs
  rwa [he] at hs

#print axioms argument_encl
end ThomsonNegative.Certificate.Correction.q03
