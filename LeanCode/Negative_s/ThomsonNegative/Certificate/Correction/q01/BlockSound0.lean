import ThomsonNegative.Certificate.Correction.q01.RowSemantics
import ThomsonNegative.Certificate.Correction.q01.Floor0
import ThomsonNegative.Certificate.Correction.q01.Congruence0_00
import ThomsonNegative.Certificate.Correction.q01.Congruence0_01
import ThomsonNegative.Certificate.Correction.q01.Congruence0_02
import ThomsonNegative.Certificate.Correction.q01.Congruence0_03
import ThomsonNegative.Certificate.Correction.q01.Congruence0_04
import ThomsonNegative.Certificate.Correction.q01.Congruence0_05
import ThomsonNegative.Certificate.Correction.q01.Congruence0_06
import ThomsonNegative.Certificate.Correction.q01.Congruence0_07
import ThomsonNegative.Certificate.Correction.q01.Congruence0_08
import ThomsonNegative.Certificate.Correction.q01.Congruence0_09
import ThomsonNegative.Certificate.Correction.q01.Congruence0_10

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def correction0 (a : ℝ) (x : Fin 68 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => Source.rowLinear a (index0 i j) x
theorem congruence0_gate (k : Fin 11) : congruenceGate context 6 ThomsonNegative.Certificate.Cells.q01.inverse0 (centerMatrix0 k)=true := by
  fin_cases k
  · exact congruence0_0_checked
  · exact congruence0_1_checked
  · exact congruence0_2_checked
  · exact congruence0_3_checked
  · exact congruence0_4_checked
  · exact congruence0_5_checked
  · exact congruence0_6_checked
  · exact congruence0_7_checked
  · exact congruence0_8_checked
  · exact congruence0_9_checked
  · exact congruence0_10_checked
theorem norm0_gate (k : Fin 11) : allBelow 6 (fun i => allBelow 6 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 6 ThomsonNegative.Certificate.Cells.q01.inverse0 (centerMatrix0 k)) i j)) (centerBound0 k i j)))=true := by
  fin_cases k
  · exact bound0_0_checked
  · exact bound0_1_checked
  · exact bound0_2_checked
  · exact bound0_3_checked
  · exact bound0_4_checked
  · exact bound0_5_checked
  · exact bound0_6_checked
  · exact bound0_7_checked
  · exact bound0_8_checked
  · exact bound0_9_checked
  · exact bound0_10_checked
theorem center_matrix0_encl (k : Fin 11) (i j : Fin 6) :
    Encl context (entry (centerMatrix0 k) i j)
      (fun t => correction0 (heightArgument t) (residualCenters residual k) i j) := by
  rw [show entry (centerMatrix0 k) i j=rowModel (index0 i j) k from entry_tabulate _ i.isLt j.isLt]
  exact row_model_encl _ k

theorem normalized_center0_bound (k : Fin 11) (i j : Fin 6) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    |(ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6 *
      correction0 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6).transpose) i j|≤
        (centerBound0 k i j:ℝ)/2^384 := by
  have h := congruenceTM_sound context_good 6 ThomsonNegative.Certificate.Cells.q01.inverse0
    (centerMatrix0 k) (fun t => correction0 (heightArgument t) (residualCenters residual k))
    (center_matrix0_encl k) (congruence0_gate k) i j
  have hb := rangeX_sound context_good h t ht
  have he := allBelow_sound _ _ (allBelow_sound _ _ (norm0_gate k) i i.isLt) j j.isLt
  have he' := Nat.eq_of_beq_eq_true he
  change rangeX context (entry (congruenceTM context 6 ThomsonNegative.Certificate.Cells.q01.inverse0 (centerMatrix0 k)) i j)=centerBound0 k i j at he'
  change |(ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6 *
      correction0 (heightArgument t) (residualCenters residual k) *
      (ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6).transpose) i j|≤
    (rangeX context (entry (congruenceTM context 6 ThomsonNegative.Certificate.Cells.q01.inverse0 (centerMatrix0 k)) i j):ℝ)/2^384 at hb
  rwa [he'] at hb

lemma majorant0_eq (i j : ℕ) : majorant0 i j=
    entryMajorant 384 6 68 11 ThomsonNegative.Certificate.Cells.q01.inverse0
      centerBound0 (fun j => (residual j).e) columnMatrix0 i j := by
  apply entryMajorantFromRaw_eq
  intro u v
  exact (rawError_match (index0 u v)).symm

theorem correction0_majorant (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (i j : Fin 6) :
    |(ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6 *
      correction0 (heightArgument t) (f t) *
      (ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6).transpose) i j|≤
        (majorant0 i j:ℝ)/2^384 := by
  rw [majorant0_eq]
  exact entryMajorant_sound ThomsonNegative.Certificate.Cells.q01.inverse0
    (fun u v => Source.rowLinear (heightArgument t) (index0 u v))
    (f t) (residualCenters residual) (fun j => (residual j).e) columnMatrix0 centerBound0
    t (abs_le.mpr ht) (residual_error f hf t ht)
    (fun u v j => row_column_bound (index0 u v) j t ht)
    (fun k i j => normalized_center0_bound k i j t ht) i j

/-- The complete finite correction proof for this block. The only remaining
premise belongs to the parent residual-identity assembly. -/
theorem correction0_floor (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∀ i : Fin 6,0<(weight0 i:ℝ)) ∧
    (∀ i : Fin 6,∑ j : Fin 6,
      |(ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6 *
        correction0 (heightArgument t) (f t) *
        (ThomsonNegative.Certificate.Cells.q01.inverse0.matrix 6).transpose) i j| *
        (weight0 j:ℝ)/(weight0 i:ℝ)≤(1:ℝ)/3) :=
  weighted_rows_of_majorant _ majorant0 weight0 (correction0_majorant f hf t ht) floor0_checked

#print axioms correction0_floor

end ThomsonNegative.Certificate.Correction.q01
