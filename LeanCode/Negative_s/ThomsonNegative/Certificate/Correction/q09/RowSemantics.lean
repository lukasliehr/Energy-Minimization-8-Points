import ThomsonNegative.Certificate.Correction.q09.Witnesses
import ThomsonNegative.Certificate.Correction.q09.InputSound
import ThomsonNegative.Certificate.Correction.SourceSound
import ThomsonNegative.Certificate.Correction.ErrorSound
import ThomsonNegative.Certificate.Correction.q09.Error00
import ThomsonNegative.Certificate.Correction.q09.Error01
import ThomsonNegative.Certificate.Correction.q09.Error02
import ThomsonNegative.Certificate.Correction.q09.Error03
import ThomsonNegative.Certificate.Correction.q09.Error04
import ThomsonNegative.Certificate.Correction.q09.Error05
import ThomsonNegative.Certificate.Correction.q09.Error06
import ThomsonNegative.Certificate.Correction.q09.Error07
import ThomsonNegative.Certificate.Correction.q09.Error08
import ThomsonNegative.Certificate.Correction.q09.Error09
import ThomsonNegative.Certificate.Correction.q09.Error10
import ThomsonNegative.Certificate.Correction.q09.Error11
import ThomsonNegative.Certificate.Correction.q09.Error12
import ThomsonNegative.Certificate.Correction.q09.Error13
import ThomsonNegative.Certificate.Correction.q09.Error14
import ThomsonNegative.Certificate.Correction.q09.Error15
import ThomsonNegative.Certificate.Correction.q09.Error16

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def heightArgument (t : ℝ) : ℝ := Compact.Target.ScalarCells.heightFunction (4:Fin 5) t-83/256
lemma rowModel_default (r : ℕ) (hr : 68≤r) (k : ℕ) : rowModel r k=zeroTM := by
  have he : r=(r-68)+68 := (Nat.sub_add_cancel hr).symm
  rw [he]
  rfl
lemma rowColumns_default (r : ℕ) (hr : 68≤r) (j : ℕ) : rowColumns r j=0 := by
  have he : r=(r-68)+68 := (Nat.sub_add_cancel hr).symm
  rw [he]
  rfl
lemma rawError_default (r : ℕ) (hr : 68≤r) : rawError r=0 := by
  have he : r=(r-68)+68 := (Nat.sub_add_cancel hr).symm
  rw [he]
  rfl

theorem row_model_encl (r : ℕ) (k : Fin 11) :
    Encl context (rowModel r k)
      (fun t => Source.rowLinear (heightArgument t) r (residualCenters residual k)) := by
  by_cases hr : r<68
  · have h := (witness_certified ⟨r,hr⟩).center_encl argument_encl k
    rw [witness_models,witness_numerator,witness_denominator] at h
    exact h.congr (fun t _ => by rw [Source.rowLinear,if_pos hr]; rfl)
  · rw [rowModel_default r (by omega)]
    exact zero_sound.congr (fun t _ => by simp [Source.rowLinear,hr])

theorem row_column_bound (r : ℕ) (j : Fin 68) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    |Source.rowLinear (heightArgument t) r (unitVector 68 j)|≤(rowColumns r j:ℝ)/2^384 := by
  by_cases hr : r<68
  · have h := (witness_certified ⟨r,hr⟩).column_bound argument_encl t ht j
    rw [witness_columns,witness_numerator,witness_denominator] at h
    simpa only [Source.rowLinear,if_pos hr,heightArgument] using h
  · rw [rowColumns_default r (by omega)]
    simp [Source.rowLinear,hr]

lemma rawError_match_fin (r : Fin 68) :
    sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns r j))=rawError r := by
  fin_cases r
  · exact rawError0_checked
  · exact rawError1_checked
  · exact rawError2_checked
  · exact rawError3_checked
  · exact rawError4_checked
  · exact rawError5_checked
  · exact rawError6_checked
  · exact rawError7_checked
  · exact rawError8_checked
  · exact rawError9_checked
  · exact rawError10_checked
  · exact rawError11_checked
  · exact rawError12_checked
  · exact rawError13_checked
  · exact rawError14_checked
  · exact rawError15_checked
  · exact rawError16_checked
  · exact rawError17_checked
  · exact rawError18_checked
  · exact rawError19_checked
  · exact rawError20_checked
  · exact rawError21_checked
  · exact rawError22_checked
  · exact rawError23_checked
  · exact rawError24_checked
  · exact rawError25_checked
  · exact rawError26_checked
  · exact rawError27_checked
  · exact rawError28_checked
  · exact rawError29_checked
  · exact rawError30_checked
  · exact rawError31_checked
  · exact rawError32_checked
  · exact rawError33_checked
  · exact rawError34_checked
  · exact rawError35_checked
  · exact rawError36_checked
  · exact rawError37_checked
  · exact rawError38_checked
  · exact rawError39_checked
  · exact rawError40_checked
  · exact rawError41_checked
  · exact rawError42_checked
  · exact rawError43_checked
  · exact rawError44_checked
  · exact rawError45_checked
  · exact rawError46_checked
  · exact rawError47_checked
  · exact rawError48_checked
  · exact rawError49_checked
  · exact rawError50_checked
  · exact rawError51_checked
  · exact rawError52_checked
  · exact rawError53_checked
  · exact rawError54_checked
  · exact rawError55_checked
  · exact rawError56_checked
  · exact rawError57_checked
  · exact rawError58_checked
  · exact rawError59_checked
  · exact rawError60_checked
  · exact rawError61_checked
  · exact rawError62_checked
  · exact rawError63_checked
  · exact rawError64_checked
  · exact rawError65_checked
  · exact rawError66_checked
  · exact rawError67_checked
lemma rawError_match (r : ℕ) :
    sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns r j))=rawError r := by
  by_cases hr : r<68
  · exact rawError_match_fin ⟨r,hr⟩
  · rw [rawError_default r (by omega)]
    simp only [rowColumns_default r (by omega),Nat.mul_zero]
    rw [sumNat_eq_sum]
    simp

theorem residual_error (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (j : Fin 68) :
    |f t j-∑ k : Fin 11,residualCenters residual k j*t^(k:ℕ)|≤((residual j).e:ℝ)/2^384 := by
  have h := (hf j).export Compact.Target.Cells.context_good t ht
  rw [poly_eq_sum] at h
  change |f t j-∑ k ∈ Finset.range 11,
    (((decode sourceContext (residual j).v).getD k 0:ℤ):ℝ)/2^384*t^k|≤
      ((residual j).e:ℝ)/2^384 at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

end ThomsonNegative.Certificate.Correction.q09
