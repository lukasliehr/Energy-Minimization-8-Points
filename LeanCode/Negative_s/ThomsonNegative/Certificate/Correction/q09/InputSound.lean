import ThomsonNegative.Certificate.Correction.q09.Input
import ThomsonNegative.Certificate.Correction.InputSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q09
set_option maxRecDepth 100000
open ThomsonNegative.Compact.Packed

/-- The actual extended root is used on the original cell parameter, even
though the correction arithmetic itself has Taylor order zero. -/
theorem argument_encl : Encl context argument
    (fun t => Compact.Target.ScalarCells.heightFunction (4:Fin 5) t-83/256) := by
  have he := sameTM_eq argument_checked
  have haok : argumentComputed.ok=true := by
    have hh := argument_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hheight := Compact.Target.ScalarCells.height_encl (4:Fin 5)
  change Encl sourceContext Compact.Target.Cells.Q09.data.heightCheckpoint
    (Compact.Target.ScalarCells.heightFunction (4:Fin 5)) at hheight
  have hs := buildArgument_sound hheight 0x51d9b79f0b59d33b9ff235bace01afec6b7511fd001650618c46f596900094c1d7457345018de24bf5ef558964542cc3 haok
  change Encl context argumentComputed _ at hs
  rwa [he] at hs

#print axioms argument_encl
end ThomsonNegative.Certificate.Correction.q09
