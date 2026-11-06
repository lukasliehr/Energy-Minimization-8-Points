import ThomsonNegative.Finalization.Cell
import ThomsonNegative.Certificate.Correction.Cells
import ThomsonNegative.Certificate.Cells.q01.Semantics
import ThomsonNegative.Certificate.Cells.q03.Semantics
import ThomsonNegative.Certificate.Cells.q05.Semantics
import ThomsonNegative.Certificate.Cells.q07.Semantics
import ThomsonNegative.Certificate.Cells.q09.Semantics

noncomputable section
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def matrixData : Fin 5 → MatrixCell :=
  ![Cells.q01.matrixData,Cells.q03.matrixData,Cells.q05.matrixData,Cells.q07.matrixData,Cells.q09.matrixData]

theorem matrix_checked (c : Fin 5) : (matrixData c).Checked c := by
  fin_cases c
  · exact Cells.q01.matrix_checked
  · exact Cells.q03.matrix_checked
  · exact Cells.q05.matrix_checked
  · exact Cells.q07.matrix_checked
  · exact Cells.q09.matrix_checked

lemma correction_size (k : Fin 4) :
    Correction.Source.blockSize (Correction.Cells.physicalBlock k)=blockSize (activeBlock k) := by
  fin_cases k <;> rfl

lemma metric_match (c : Fin 5) (k : Fin 4) :
    (matrixData c).metric (activeBlock k).val=Correction.Cells.metric c k := by
  fin_cases c <;> fin_cases k <;> rfl

lemma residual_match (c : Fin 5) (j : Fin 68) :
    (matrixData c).residualCheckpoint.getD j.val zeroTM=Correction.Cells.residual c j.val := by
  fin_cases c <;> rfl

theorem residual_encl (c : Fin 5) (j : Fin 68) :
    Encl Correction.sourceContext (Correction.Cells.residual c j.val)
      (fun t => (matrixData c).sourceResidual c t j) := by
  rw [← residual_match]
  exact MatrixCell.residual_encl (matrix_checked c) j

def fourFloors (c : Fin 5) : FourFloors (matrixData c) c where
  inverse := Correction.Cells.inverse c
  weight := fun k i => (Correction.Cells.weight c k i.val:ℝ)
  metric_order := by
    intro k
    rw [metric_match,Correction.Cells.metric_order,correction_size]
  metric_inverse := by
    intro k
    rw [metric_match]
    have h := Correction.Cells.metric_inverse c k
    rw [correction_size] at h
    exact h
  positive_weights := by
    intro k
    have ht : (0:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by norm_num
    fin_cases k
    · exact (Correction.Cells.certified_floor c 0 ((matrixData c).sourceResidual c) (residual_encl c) 0 ht).1
    · exact (Correction.Cells.certified_floor c 1 ((matrixData c).sourceResidual c) (residual_encl c) 0 ht).1
    · exact (Correction.Cells.certified_floor c 2 ((matrixData c).sourceResidual c) (residual_encl c) 0 ht).1
    · exact (Correction.Cells.certified_floor c 3 ((matrixData c).sourceResidual c) (residual_encl c) 0 ht).1
  rows := by
    intro t ht k
    fin_cases k
    · exact (Correction.Cells.certified_floor c 0 ((matrixData c).sourceResidual c) (residual_encl c) t ht).2
    · exact (Correction.Cells.certified_floor c 1 ((matrixData c).sourceResidual c) (residual_encl c) t ht).2
    · exact (Correction.Cells.certified_floor c 2 ((matrixData c).sourceResidual c) (residual_encl c) t ht).2
    · exact (Correction.Cells.certified_floor c 3 ((matrixData c).sourceResidual c) (residual_encl c) t ht).2

theorem checked_corrected_psd (c : Fin 5) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (b : Block) :
    (correctedFamily (matrixData c) c t b).PosSemidef :=
  correctedFamily_psd (matrixData c) c (fourFloors c) t ht b

#print axioms fourFloors
#print axioms checked_corrected_psd
end ThomsonNegative.Finalization
