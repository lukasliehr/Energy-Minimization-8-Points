import ThomsonNegative.Certificate.Correction.q05.RowSemantics
import ThomsonNegative.Certificate.Correction.q05.Floor7
import ThomsonNegative.Certificate.Correction.q05.Congruence7_00
import ThomsonNegative.Certificate.Correction.q05.Congruence7_01
import ThomsonNegative.Certificate.Correction.q05.Congruence7_02
import ThomsonNegative.Certificate.Correction.q05.Congruence7_03
import ThomsonNegative.Certificate.Correction.q05.Congruence7_04
import ThomsonNegative.Certificate.Correction.q05.Congruence7_05
import ThomsonNegative.Certificate.Correction.q05.Congruence7_06
import ThomsonNegative.Certificate.Correction.q05.Congruence7_07
import ThomsonNegative.Certificate.Correction.q05.Congruence7_08
import ThomsonNegative.Certificate.Correction.q05.Congruence7_09
import ThomsonNegative.Certificate.Correction.q05.Congruence7_10

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def correction7 (a : ℝ) (x : Fin 68 → ℝ) : Matrix (Fin 11) (Fin 11) ℝ :=
  fun i j => Source.rowLinear a (index7 i j) x
theorem congruence7_gate (k : Fin 11) : congruenceGate context 11 ThomsonNegative.Certificate.Cells.q05.inverse7 (centerMatrix7 k)=true := by
  fin_cases k
  · exact congruence7_0_checked
  · exact congruence7_1_checked
  · exact congruence7_2_checked
  · exact congruence7_3_checked
  · exact congruence7_4_checked
  · exact congruence7_5_checked
  · exact congruence7_6_checked
  · exact congruence7_7_checked
  · exact congruence7_8_checked
  · exact congruence7_9_checked
  · exact congruence7_10_checked
theorem norm7_gate (k : Fin 11) : allBelow 11 (fun i => allBelow 11 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q05.inverse7 (centerMatrix7 k)) i j)) (centerBound7 k i j)))=true := by
  fin_cases k
  · exact bound7_0_checked
  · exact bound7_1_checked
  · exact bound7_2_checked
  · exact bound7_3_checked
  · exact bound7_4_checked
  · exact bound7_5_checked
  · exact bound7_6_checked
  · exact bound7_7_checked
  · exact bound7_8_checked
  · exact bound7_9_checked
  · exact bound7_10_checked
theorem center_matrix7_encl (k : Fin 11) (i j : Fin 11) :
    Encl context (entry (centerMatrix7 k) i j)
      (fun t => correction7 (heightArgument t) (residualCenters residual k) i j) := by
  rw [show entry (centerMatrix7 k) i j=rowModel (index7 i j) k from entry_tabulate _ i.isLt j.isLt]
  exact row_model_encl _ k

theorem normalized_center7_bound (k : Fin 11) (i j : Fin 11) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    |(ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11 *
      correction7 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11).transpose) i j|≤
        (centerBound7 k i j:ℝ)/2^384 := by
  have h := congruenceTM_sound context_good 11 ThomsonNegative.Certificate.Cells.q05.inverse7
    (centerMatrix7 k) (fun t => correction7 (heightArgument t) (residualCenters residual k))
    (center_matrix7_encl k) (congruence7_gate k) i j
  have hb := rangeX_sound context_good h t ht
  have he := allBelow_sound _ _ (allBelow_sound _ _ (norm7_gate k) i i.isLt) j j.isLt
  have he' := Nat.eq_of_beq_eq_true he
  change rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q05.inverse7 (centerMatrix7 k)) i j)=centerBound7 k i j at he'
  change |(ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11 *
      correction7 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11).transpose) i j|≤
    (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q05.inverse7 (centerMatrix7 k)) i j):ℝ)/2^384 at hb
  rwa [he'] at hb

lemma majorant7_eq (i j : ℕ) : majorant7 i j=
    entryMajorant 384 11 68 11 ThomsonNegative.Certificate.Cells.q05.inverse7
      centerBound7 (fun j => (residual j).e) columnMatrix7 i j := by
  apply entryMajorantFromRaw_eq
  intro u v
  exact (rawError_match (index7 u v)).symm

theorem correction7_majorant (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (i j : Fin 11) :
    |(ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11 *
      correction7 (heightArgument t) (f t) *
      (ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11).transpose) i j|≤
        (majorant7 i j:ℝ)/2^384 := by
  rw [majorant7_eq]
  exact entryMajorant_sound ThomsonNegative.Certificate.Cells.q05.inverse7
    (fun u v => Source.rowLinear (heightArgument t) (index7 u v))
    (f t) (residualCenters residual) (fun j => (residual j).e) columnMatrix7 centerBound7
    t (abs_le.mpr ht) (residual_error f hf t ht)
    (fun u v j => row_column_bound (index7 u v) j t ht)
    (fun k i j => normalized_center7_bound k i j t ht) i j

/-- The complete finite correction proof for this block. The only remaining
premise belongs to the parent residual-identity assembly. -/
theorem correction7_floor (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∀ i : Fin 11,0<(weight7 i:ℝ)) ∧
    (∀ i : Fin 11,∑ j : Fin 11,
      |(ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11 *
        correction7 (heightArgument t) (f t) *
        (ThomsonNegative.Certificate.Cells.q05.inverse7.matrix 11).transpose) i j| *
        (weight7 j:ℝ)/(weight7 i:ℝ)≤(1:ℝ)/3) :=
  weighted_rows_of_majorant _ majorant7 weight7 (correction7_majorant f hf t ht) floor7_checked

#print axioms correction7_floor

end ThomsonNegative.Certificate.Correction.q05
