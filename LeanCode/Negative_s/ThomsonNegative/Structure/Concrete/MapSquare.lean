import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapSquare
open ThomsonNegative.Structure.Exact
noncomputable def rawDen0 : Nat := 0x3500601000
noncomputable def rawDen1 : Nat := 0x700301000
noncomputable def rawDen2 : Nat := 0x700301000
noncomputable def rawDen3 : Nat := 0x700301000
noncomputable def rawDen4 : Nat := 0x700301000
noncomputable def rawDen5 : Nat := 0x700301000
noncomputable def rawDen6 : Nat := 0x300201000
noncomputable def rawDen7 : Nat := 0xd100801000
noncomputable def rawDen : Nat → Nat
 | 0 => rawDen0
 | 1 => rawDen1
 | 2 => rawDen2
 | 3 => rawDen3
 | 4 => rawDen4
 | 5 => rawDen5
 | 6 => rawDen6
 | 7 => rawDen7
 | _ => oneRecord
noncomputable def equation (b : Nat) : Equation :=
  ⟨218,30,61,1,(fun _ => BasisData.denominator b),
    (fun _ => BasisData.denominator b),rawDen b,MapKernel.basisSquare b,oneRecord,oneRecord⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block0 : (equation 0).check=true := by decide +kernel
theorem block1 : (equation 1).check=true := by decide +kernel
theorem block2 : (equation 2).check=true := by decide +kernel
theorem block3 : (equation 3).check=true := by decide +kernel
theorem block4 : (equation 4).check=true := by decide +kernel
theorem block5 : (equation 5).check=true := by decide +kernel
theorem block6 : (equation 6).check=true := by decide +kernel
theorem block7 : (equation 7).check=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapSquare
