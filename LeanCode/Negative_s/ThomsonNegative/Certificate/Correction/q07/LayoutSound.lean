import ThomsonNegative.Certificate.Correction.SourceBlock
import ThomsonNegative.Certificate.Correction.q07.BlockSound0
import ThomsonNegative.Certificate.Correction.q07.BlockSound1
import ThomsonNegative.Certificate.Correction.q07.BlockSound6
import ThomsonNegative.Certificate.Correction.q07.BlockSound7

noncomputable section
namespace ThomsonNegative.Certificate.Correction.q07
theorem index0_shared (i j : ℕ) : index0 i j=Source.blockIndex 0 i j := rfl
theorem correction0_shared (u : ℝ) (x : Fin 68 → ℝ) : correction0 u x=Source.blockLinear u (0:Fin 8) x := rfl
theorem correction0_symmetric (u : ℝ) (x : Fin 68 → ℝ) (i j : Fin 6) :
    correction0 u x i j=correction0 u x j i := by
  rw [correction0_shared]
  exact Source.blockLinear_symmetric u (0:Fin 8) x i j
theorem index1_shared (i j : ℕ) : index1 i j=Source.blockIndex 1 i j := rfl
theorem correction1_shared (u : ℝ) (x : Fin 68 → ℝ) : correction1 u x=Source.blockLinear u (1:Fin 8) x := rfl
theorem correction1_symmetric (u : ℝ) (x : Fin 68 → ℝ) (i j : Fin 5) :
    correction1 u x i j=correction1 u x j i := by
  rw [correction1_shared]
  exact Source.blockLinear_symmetric u (1:Fin 8) x i j
theorem index6_shared (i j : ℕ) : index6 i j=Source.blockIndex 6 i j := rfl
theorem correction6_shared (u : ℝ) (x : Fin 68 → ℝ) : correction6 u x=Source.blockLinear u (6:Fin 8) x := rfl
theorem correction6_symmetric (u : ℝ) (x : Fin 68 → ℝ) (i j : Fin 11) :
    correction6 u x i j=correction6 u x j i := by
  rw [correction6_shared]
  exact Source.blockLinear_symmetric u (6:Fin 8) x i j
theorem index7_shared (i j : ℕ) : index7 i j=Source.blockIndex 7 i j := rfl
theorem correction7_shared (u : ℝ) (x : Fin 68 → ℝ) : correction7 u x=Source.blockLinear u (7:Fin 8) x := rfl
theorem correction7_symmetric (u : ℝ) (x : Fin 68 → ℝ) (i j : Fin 11) :
    correction7 u x i j=correction7 u x j i := by
  rw [correction7_shared]
  exact Source.blockLinear_symmetric u (7:Fin 8) x i j
end ThomsonNegative.Certificate.Correction.q07
