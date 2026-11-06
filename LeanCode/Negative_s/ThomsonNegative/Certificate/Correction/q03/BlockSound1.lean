import ThomsonNegative.Certificate.Correction.q03.RowSemantics
import ThomsonNegative.Certificate.Correction.q03.Floor1
import ThomsonNegative.Certificate.Correction.q03.Congruence1_00
import ThomsonNegative.Certificate.Correction.q03.Congruence1_01
import ThomsonNegative.Certificate.Correction.q03.Congruence1_02
import ThomsonNegative.Certificate.Correction.q03.Congruence1_03
import ThomsonNegative.Certificate.Correction.q03.Congruence1_04
import ThomsonNegative.Certificate.Correction.q03.Congruence1_05
import ThomsonNegative.Certificate.Correction.q03.Congruence1_06
import ThomsonNegative.Certificate.Correction.q03.Congruence1_07
import ThomsonNegative.Certificate.Correction.q03.Congruence1_08
import ThomsonNegative.Certificate.Correction.q03.Congruence1_09
import ThomsonNegative.Certificate.Correction.q03.Congruence1_10

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def correction1 (a : ℝ) (x : Fin 68 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => Source.rowLinear a (index1 i j) x
theorem congruence1_gate (k : Fin 11) : congruenceGate context 5 ThomsonNegative.Certificate.Cells.q03.inverse1 (centerMatrix1 k)=true := by
  fin_cases k
  · exact congruence1_0_checked
  · exact congruence1_1_checked
  · exact congruence1_2_checked
  · exact congruence1_3_checked
  · exact congruence1_4_checked
  · exact congruence1_5_checked
  · exact congruence1_6_checked
  · exact congruence1_7_checked
  · exact congruence1_8_checked
  · exact congruence1_9_checked
  · exact congruence1_10_checked
theorem norm1_gate (k : Fin 11) : allBelow 5 (fun i => allBelow 5 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q03.inverse1 (centerMatrix1 k)) i j)) (centerBound1 k i j)))=true := by
  fin_cases k
  · exact bound1_0_checked
  · exact bound1_1_checked
  · exact bound1_2_checked
  · exact bound1_3_checked
  · exact bound1_4_checked
  · exact bound1_5_checked
  · exact bound1_6_checked
  · exact bound1_7_checked
  · exact bound1_8_checked
  · exact bound1_9_checked
  · exact bound1_10_checked
theorem center_matrix1_encl (k : Fin 11) (i j : Fin 5) :
    Encl context (entry (centerMatrix1 k) i j)
      (fun t => correction1 (heightArgument t) (residualCenters residual k) i j) := by
  rw [show entry (centerMatrix1 k) i j=rowModel (index1 i j) k from entry_tabulate _ i.isLt j.isLt]
  exact row_model_encl _ k

theorem normalized_center1_bound (k : Fin 11) (i j : Fin 5) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    |(ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5 *
      correction1 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5).transpose) i j|≤
        (centerBound1 k i j:ℝ)/2^384 := by
  have h := congruenceTM_sound context_good 5 ThomsonNegative.Certificate.Cells.q03.inverse1
    (centerMatrix1 k) (fun t => correction1 (heightArgument t) (residualCenters residual k))
    (center_matrix1_encl k) (congruence1_gate k) i j
  have hb := rangeX_sound context_good h t ht
  have he := allBelow_sound _ _ (allBelow_sound _ _ (norm1_gate k) i i.isLt) j j.isLt
  have he' := Nat.eq_of_beq_eq_true he
  change rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q03.inverse1 (centerMatrix1 k)) i j)=centerBound1 k i j at he'
  change |(ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5 *
      correction1 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5).transpose) i j|≤
    (rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q03.inverse1 (centerMatrix1 k)) i j):ℝ)/2^384 at hb
  rwa [he'] at hb

lemma majorant1_eq (i j : ℕ) : majorant1 i j=
    entryMajorant 384 5 68 11 ThomsonNegative.Certificate.Cells.q03.inverse1
      centerBound1 (fun j => (residual j).e) columnMatrix1 i j := by
  apply entryMajorantFromRaw_eq
  intro u v
  exact (rawError_match (index1 u v)).symm

theorem correction1_majorant (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (i j : Fin 5) :
    |(ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5 *
      correction1 (heightArgument t) (f t) *
      (ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5).transpose) i j|≤
        (majorant1 i j:ℝ)/2^384 := by
  rw [majorant1_eq]
  exact entryMajorant_sound ThomsonNegative.Certificate.Cells.q03.inverse1
    (fun u v => Source.rowLinear (heightArgument t) (index1 u v))
    (f t) (residualCenters residual) (fun j => (residual j).e) columnMatrix1 centerBound1
    t (abs_le.mpr ht) (residual_error f hf t ht)
    (fun u v j => row_column_bound (index1 u v) j t ht)
    (fun k i j => normalized_center1_bound k i j t ht) i j

/-- The complete finite correction proof for this block. The only remaining
premise belongs to the parent residual-identity assembly. -/
theorem correction1_floor (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∀ i : Fin 5,0<(weight1 i:ℝ)) ∧
    (∀ i : Fin 5,∑ j : Fin 5,
      |(ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5 *
        correction1 (heightArgument t) (f t) *
        (ThomsonNegative.Certificate.Cells.q03.inverse1.matrix 5).transpose) i j| *
        (weight1 j:ℝ)/(weight1 i:ℝ)≤(1:ℝ)/3) :=
  weighted_rows_of_majorant _ majorant1 weight1 (correction1_majorant f hf t ht) floor1_checked

#print axioms correction1_floor

end ThomsonNegative.Certificate.Correction.q03
