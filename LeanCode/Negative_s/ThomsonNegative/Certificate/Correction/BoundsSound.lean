import ThomsonNegative.Certificate.Correction.BoundsKernel
import ThomsonNegative.Certificate.ResidualBound
import ThomsonNegative.Certificate.MetricSound
import ThomsonNegative.Compact.Packed.Comp

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

lemma sumNat_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    sumNat n f=∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumNat n f + f n = _
    rw [ih,Finset.sum_range_succ]

lemma sumNat_cast (n : ℕ) (f : ℕ → ℕ) :
    (sumNat n f:ℝ)=∑ i : Fin n, (f i:ℝ) := by
  rw [sumNat_eq_sum, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]

lemma rowCheck_spec (S n : ℕ) (majorant : ℕ → ℕ → ℕ) (weight : ℕ → ℕ)
    (h : rowCheck S n majorant weight=true) :
    (∀ i : Fin n,0<(weight i:ℝ)) ∧
    (∀ i : Fin n,∑ j : Fin n,
      ((majorant i j:ℝ)/2^S)*(weight j:ℝ)/(weight i:ℝ)≤(1:ℝ)/3) := by
  have hall : ∀ i < n, (Nat.blt 0 (weight i) &&
      Nat.ble (Nat.mul 3 (sumNat n (fun j => Nat.mul (majorant i j) (weight j))))
        (Nat.mul (Nat.pow 2 S) (weight i)))=true := by
    exact allBelow_sound _ _ h
  have hw (i : Fin n) : 0 < weight i := by
    have hh := hall i i.isLt
    simp only [Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hh
    exact hh.1
  refine ⟨fun i => by exact_mod_cast hw i, ?_⟩
  intro i
  have hh := hall i i.isLt
  simp only [Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hh
  have hn : 3*sumNat n (fun j => majorant i j*weight j) ≤ 2^S*weight i := by
    exact hh.2
  have hr : (3:ℝ)*(∑ j : Fin n, (majorant i j:ℝ)*(weight j:ℝ))≤2^S*(weight i:ℝ) := by
    have hcast : (3:ℝ)*(sumNat n (fun j => majorant i j*weight j):ℝ)≤2^S*(weight i:ℝ) := by
      exact_mod_cast hn
    simpa only [sumNat_cast,Nat.cast_mul] using hcast
  have hp : (0:ℝ)<2^S := pow_pos (by norm_num) _
  have hwi : (0:ℝ)<(weight i:ℝ) := by exact_mod_cast hw i
  calc
    _ = (∑ j : Fin n,(majorant i j:ℝ)*(weight j:ℝ))/(2^S*(weight i:ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 1/3 := by
      apply (div_le_iff₀ (mul_pos hp hwi)).mpr
      linarith

/-- A row-check leaf turns any verified entry majorant into the same uniform
one-third bound. Its weight search has no semantic role in the proof. -/
theorem weighted_rows_of_majorant {n S : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (M : ℕ → ℕ → ℕ) (w : ℕ → ℕ)
    (hM : ∀ i j, |C i j|≤(M i j:ℝ)/2^S)
    (hcheck : rowCheck S n M w=true) :
    (∀ i : Fin n,0<(w i:ℝ)) ∧
    (∀ i : Fin n,∑ j : Fin n,|C i j| * (w j:ℝ)/(w i:ℝ)≤(1:ℝ)/3) := by
  obtain ⟨hw,hrow⟩ := rowCheck_spec S n M w hcheck
  refine ⟨hw,fun i => le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hrow i)⟩
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM i j) (hw j).le) (hw i).le

lemma ceilShift_bound (s x : ℕ) : (x:ℝ)/2^s≤(ceilShift s x:ℝ) := by
  exact le_cdiv s x

#print axioms rowCheck_spec
#print axioms weighted_rows_of_majorant
end ThomsonNegative.Certificate.Correction

namespace ThomsonNegative.Certificate.Correction

lemma entryMajorantFromRaw_eq (S n inputs centers : ℕ) (J : FactorData)
    (bound : ℕ → ℕ → ℕ → ℕ) (error : ℕ → ℕ)
    (column : ℕ → ℕ → ℕ → ℕ) (raw : ℕ → ℕ → ℕ)
    (hraw : ∀ u v, raw u v=errorNumerator inputs error column u v) (i j : ℕ) :
    entryMajorantFromRaw S n centers J bound raw i j=
      entryMajorant S n inputs centers J bound error column i j := by
  unfold entryMajorantFromRaw entryMajorant congruenceFromRaw congruenceErrorNumerator
  simp only [hraw]

end ThomsonNegative.Certificate.Correction
