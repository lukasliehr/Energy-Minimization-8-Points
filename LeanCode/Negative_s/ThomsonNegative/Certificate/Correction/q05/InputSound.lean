import ThomsonNegative.Certificate.Correction.q05.Input
import ThomsonNegative.Certificate.Correction.InputSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q05
set_option maxRecDepth 100000
open ThomsonNegative.Compact.Packed

/-- The actual extended root is used on the original cell parameter, even
though the correction arithmetic itself has Taylor order zero. -/
theorem argument_encl : Encl context argument
    (fun t => Compact.Target.ScalarCells.heightFunction (2:Fin 5) t-83/256) := by
  have he := sameTM_eq argument_checked
  have haok : argumentComputed.ok=true := by
    have hh := argument_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hheight := Compact.Target.ScalarCells.height_encl (2:Fin 5)
  change Encl sourceContext Compact.Target.Cells.Q05.data.heightCheckpoint
    (Compact.Target.ScalarCells.heightFunction (2:Fin 5)) at hheight
  have hs := buildArgument_sound hheight 0x52c96a9674bd7b099e7e68bd39ae3294d747f678bb630cc4f07b834cd5fde1a77e25e93e5b18165f59c7bb59851145a3 haok
  change Encl context argumentComputed _ at hs
  rwa [he] at hs

#print axioms argument_encl
end ThomsonNegative.Certificate.Correction.q05
