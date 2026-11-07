import ThomsonNegative.Certificate.Correction.q01.RowSemantics
import ThomsonNegative.Certificate.Correction.q01.Floor6
import ThomsonNegative.Certificate.Correction.q01.Congruence6_00
import ThomsonNegative.Certificate.Correction.q01.Congruence6_01
import ThomsonNegative.Certificate.Correction.q01.Congruence6_02
import ThomsonNegative.Certificate.Correction.q01.Congruence6_03
import ThomsonNegative.Certificate.Correction.q01.Congruence6_04
import ThomsonNegative.Certificate.Correction.q01.Congruence6_05
import ThomsonNegative.Certificate.Correction.q01.Congruence6_06
import ThomsonNegative.Certificate.Correction.q01.Congruence6_07
import ThomsonNegative.Certificate.Correction.q01.Congruence6_08
import ThomsonNegative.Certificate.Correction.q01.Congruence6_09
import ThomsonNegative.Certificate.Correction.q01.Congruence6_10

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def correction6 (a : ℝ) (x : Fin 68 → ℝ) : Matrix (Fin 11) (Fin 11) ℝ :=
  fun i j => Source.rowLinear a (index6 i j) x
theorem congruence6_gate (k : Fin 11) : congruenceGate context 11 ThomsonNegative.Certificate.Cells.q01.inverse6 (centerMatrix6 k)=true := by
  fin_cases k
  · exact congruence6_0_checked
  · exact congruence6_1_checked
  · exact congruence6_2_checked
  · exact congruence6_3_checked
  · exact congruence6_4_checked
  · exact congruence6_5_checked
  · exact congruence6_6_checked
  · exact congruence6_7_checked
  · exact congruence6_8_checked
  · exact congruence6_9_checked
  · exact congruence6_10_checked
theorem norm6_gate (k : Fin 11) : allBelow 11 (fun i => allBelow 11 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q01.inverse6 (centerMatrix6 k)) i j)) (centerBound6 k i j)))=true := by
  fin_cases k
  · exact bound6_0_checked
  · exact bound6_1_checked
  · exact bound6_2_checked
  · exact bound6_3_checked
  · exact bound6_4_checked
  · exact bound6_5_checked
  · exact bound6_6_checked
  · exact bound6_7_checked
  · exact bound6_8_checked
  · exact bound6_9_checked
  · exact bound6_10_checked
theorem center_matrix6_encl (k : Fin 11) (i j : Fin 11) :
    Encl context (entry (centerMatrix6 k) i j)
      (fun t => correction6 (heightArgument t) (residualCenters residual k) i j) := by
  rw [show entry (centerMatrix6 k) i j=rowModel (index6 i j) k from entry_tabulate _ i.isLt j.isLt]
  exact row_model_encl _ k

theorem normalized_center6_bound (k : Fin 11) (i j : Fin 11) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    |(ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11 *
      correction6 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11).transpose) i j|≤
        (centerBound6 k i j:ℝ)/2^384 := by
  have h := congruenceTM_sound context_good 11 ThomsonNegative.Certificate.Cells.q01.inverse6
    (centerMatrix6 k) (fun t => correction6 (heightArgument t) (residualCenters residual k))
    (center_matrix6_encl k) (congruence6_gate k) i j
  have hb := rangeX_sound context_good h t ht
  have he := allBelow_sound _ _ (allBelow_sound _ _ (norm6_gate k) i i.isLt) j j.isLt
  have he' := Nat.eq_of_beq_eq_true he
  change rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q01.inverse6 (centerMatrix6 k)) i j)=centerBound6 k i j at he'
  change |(ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11 *
      correction6 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11).transpose) i j|≤
    (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q01.inverse6 (centerMatrix6 k)) i j):ℝ)/2^384 at hb
  rwa [he'] at hb

lemma majorant6_eq (i j : ℕ) : majorant6 i j=
    entryMajorant 384 11 68 11 ThomsonNegative.Certificate.Cells.q01.inverse6
      centerBound6 (fun j => (residual j).e) columnMatrix6 i j := by
  apply entryMajorantFromRaw_eq
  intro u v
  exact (rawError_match (index6 u v)).symm

theorem correction6_majorant (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (i j : Fin 11) :
    |(ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11 *
      correction6 (heightArgument t) (f t) *
      (ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11).transpose) i j|≤
        (majorant6 i j:ℝ)/2^384 := by
  rw [majorant6_eq]
  exact entryMajorant_sound ThomsonNegative.Certificate.Cells.q01.inverse6
    (fun u v => Source.rowLinear (heightArgument t) (index6 u v))
    (f t) (residualCenters residual) (fun j => (residual j).e) columnMatrix6 centerBound6
    t (abs_le.mpr ht) (residual_error f hf t ht)
    (fun u v j => row_column_bound (index6 u v) j t ht)
    (fun k i j => normalized_center6_bound k i j t ht) i j

/-- The complete finite correction proof for this block. The only remaining
premise belongs to the parent residual-identity assembly. -/
theorem correction6_floor (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∀ i : Fin 11,0<(weight6 i:ℝ)) ∧
    (∀ i : Fin 11,∑ j : Fin 11,
      |(ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11 *
        correction6 (heightArgument t) (f t) *
        (ThomsonNegative.Certificate.Cells.q01.inverse6.matrix 11).transpose) i j| *
        (weight6 j:ℝ)/(weight6 i:ℝ)≤(1:ℝ)/3) :=
  weighted_rows_of_majorant _ majorant6 weight6 (correction6_majorant f hf t ht) floor6_checked

#print axioms correction6_floor

end ThomsonNegative.Certificate.Correction.q01
