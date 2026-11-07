import ThomsonNegative.Certificate.Correction.q07.Input
import ThomsonNegative.Certificate.Correction.InputSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q07
set_option maxRecDepth 100000
open ThomsonNegative.Compact.Packed

/-- The actual extended root is used on the original cell parameter, even
though the correction arithmetic itself has Taylor order zero. -/
theorem argument_encl : Encl context argument
    (fun t => Compact.Target.ScalarCells.heightFunction (3:Fin 5) t-83/256) := by
  have he := sameTM_eq argument_checked
  have haok : argumentComputed.ok=true := by
    have hh := argument_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hheight := Compact.Target.ScalarCells.height_encl (3:Fin 5)
  change Encl sourceContext Compact.Target.Cells.Q07.data.heightCheckpoint
    (Compact.Target.ScalarCells.heightFunction (3:Fin 5)) at hheight
  have hs := buildArgument_sound hheight 0x52530322cdd7498945caff93967f2e166be63662545eeb2a4005665452cf2020e7433dbe10bc2788dfdc5d7d8207f2d3 haok
  change Encl context argumentComputed _ at hs
  rwa [he] at hs

#print axioms argument_encl
end ThomsonNegative.Certificate.Correction.q07
