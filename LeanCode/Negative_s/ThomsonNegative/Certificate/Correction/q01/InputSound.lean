import ThomsonNegative.Certificate.Correction.q01.Input
import ThomsonNegative.Certificate.Correction.InputSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q01
set_option maxRecDepth 100000
open ThomsonNegative.Compact.Packed

/-- The actual extended root is used on the original cell parameter, even
though the correction arithmetic itself has Taylor order zero. -/
theorem argument_encl : Encl context argument
    (fun t => Compact.Target.ScalarCells.heightFunction (0:Fin 5) t-83/256) := by
  have he := sameTM_eq argument_checked
  have haok : argumentComputed.ok=true := by
    have hh := argument_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hheight := Compact.Target.ScalarCells.height_encl (0:Fin 5)
  change Encl sourceContext Compact.Target.Cells.Q01.data.heightCheckpoint
    (Compact.Target.ScalarCells.heightFunction (0:Fin 5)) at hheight
  have hs := buildArgument_sound hheight 0x53a827363cba782e90608656ec105e62aeef90f20f89638a461411f99d06a120a6799b54d137a817017be590ceb02130 haok
  change Encl context argumentComputed _ at hs
  rwa [he] at hs

#print axioms argument_encl
end ThomsonNegative.Certificate.Correction.q01
