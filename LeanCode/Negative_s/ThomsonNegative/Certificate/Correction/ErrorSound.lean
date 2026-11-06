import ThomsonNegative.Certificate.Correction.BoundsSound
import ThomsonNegative.Certificate.Correction.CongruenceSound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

lemma metricMagnitude_bound (J : FactorData) (i j : ℕ) :
    |J.eval i j|≤(metricMagnitude J i j:ℝ)/2^J.bits := by
  rw [FactorData.eval,abs_div,abs_of_pos (show (0:ℝ)<2^J.bits from pow_pos (by norm_num) _)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold pairReal metricMagnitude
  push_cast
  have hp : (0:ℝ)≤(factorEntry J i j).1 := Nat.cast_nonneg _
  have hn : (0:ℝ)≤(factorEntry J i j).2 := Nat.cast_nonneg _
  simpa only [Nat.add_eq,Nat.cast_add,sub_zero,zero_sub,abs_neg,abs_of_nonneg hp,abs_of_nonneg hn] using
    (abs_sub_le ((factorEntry J i j).1:ℝ) 0 ((factorEntry J i j).2:ℝ))

lemma errorNumerator_bound {inputs S : ℕ}
    (L : (Fin inputs → ℝ) →ₗ[ℝ] ℝ) (v : Fin inputs → ℝ)
    (error : ℕ → ℕ) (column : ℕ → ℕ → ℕ → ℕ) (u w : ℕ)
    (hv : ∀ j, |v j|≤(error j:ℝ)/2^S)
    (hc : ∀ j, |L (unitVector inputs j)|≤(column u w j:ℝ)/2^S) :
    |L v|≤(errorNumerator inputs error column u w:ℝ)/(2^S*2^S) := by
  have h := linearMap_box_bound L v
    (fun j => (error j:ℝ)/2^S) (fun j => (column u w j:ℝ)/2^S) hv hc
  refine h.trans_eq ?_
  simp only [errorNumerator,Nat.mul_eq,sumNat_cast,Nat.cast_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma congruence_entry_eq {n : ℕ} (J E : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (J*E*J.transpose) i j=∑ u,∑ v,J i u*E u v*J j v := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma congruence_abs_le {n : ℕ} (J E M : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ u v, |E u v|≤M u v) (i j : Fin n) :
    |(J*E*J.transpose) i j|≤∑ u,∑ v,|J i u| * M u v*|J j v| := by
  rw [congruence_entry_eq]
  calc
    _ ≤ ∑ u, |∑ v,J i u*E u v*J j v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u,∑ v,|J i u*E u v*J j v| := Finset.sum_le_sum
      (fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE u v) (abs_nonneg _)) (abs_nonneg _)

/-- All independent residual errors survive both exact metric multiplications. -/
theorem congruence_error_bound {n inputs S : ℕ} (J : FactorData)
    (E : Matrix (Fin n) (Fin n) ℝ) (error : ℕ → ℕ)
    (column : ℕ → ℕ → ℕ → ℕ)
    (hE : ∀ u v, |E u v|≤(errorNumerator inputs error column u v:ℝ)/(2^S*2^S))
    (i j : Fin n) :
    |(J.matrix n*E*(J.matrix n).transpose) i j|≤
      (ceilShift (S+2*J.bits) (congruenceErrorNumerator n inputs J error column i j):ℝ)/2^S := by
  have h := congruence_abs_le (J.matrix n) E
    (fun u v => (errorNumerator inputs error column u v:ℝ)/(2^S*2^S)) hE i j
  have hmajor :
      (∑ u : Fin n,∑ v : Fin n, |J.matrix n i u| * 
        ((errorNumerator inputs error column u v:ℝ)/(2^S*2^S))*|J.matrix n j v|) ≤
      ∑ u : Fin n,∑ v : Fin n,
        ((metricMagnitude J i u:ℝ)/2^J.bits)*
        ((errorNumerator inputs error column u v:ℝ)/(2^S*2^S))*
        ((metricMagnitude J j v:ℝ)/2^J.bits) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (metricMagnitude_bound J i u) (by positivity))
      (metricMagnitude_bound J j v) (abs_nonneg _) (by positivity)
  have heq :
      (∑ u : Fin n,∑ v : Fin n,
        ((metricMagnitude J i u:ℝ)/2^J.bits)*
        ((errorNumerator inputs error column u v:ℝ)/(2^S*2^S))*
        ((metricMagnitude J j v:ℝ)/2^J.bits)) =
      ((congruenceErrorNumerator n inputs J error column i j:ℝ)/2^(S+2*J.bits))/2^S := by
    simp only [congruenceErrorNumerator,Nat.mul_eq,sumNat_cast,Nat.cast_mul,
      Finset.sum_div,show 2*J.bits=J.bits+J.bits by omega,pow_add]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  exact (h.trans hmajor).trans (heq.trans_le
    (div_le_div_of_nonneg_right (ceilShift_bound _ _) (by positivity)))

/-- Entry of congruence as a linear map on coefficient residuals. -/
def normalizedMap {n inputs : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (D : Fin n → Fin n → (Fin inputs → ℝ) →ₗ[ℝ] ℝ) (i j : Fin n) :
    (Fin inputs → ℝ) →ₗ[ℝ] ℝ :=
  ∑ u, ∑ v, (J i u*J j v) • D u v

lemma normalizedMap_apply {n inputs : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (D : Fin n → Fin n → (Fin inputs → ℝ) →ₗ[ℝ] ℝ) (i j : Fin n)
    (x : Fin inputs → ℝ) :
    normalizedMap J D i j x=(J*(Matrix.of (fun u v => D u v x))*J.transpose) i j := by
  rw [congruence_entry_eq]
  simp only [Matrix.of_apply,normalizedMap,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma polynomial_remainder_bound {inputs degree : ℕ}
    (L : (Fin inputs → ℝ) →ₗ[ℝ] ℝ) (r : Fin inputs → ℝ)
    (center : Fin degree → Fin inputs → ℝ) (bound : Fin degree → ℝ)
    (t E : ℝ) (ht : |t|≤1)
    (he : |L (r-∑ k : Fin degree,t^(k:ℕ) • center k)|≤E)
    (hc : ∀ k,|L (center k)|≤bound k) :
    |L r|≤(∑ k,bound k)+E := by
  let p : Fin inputs → ℝ := ∑ k : Fin degree,t^(k:ℕ) • center k
  have hp : |L p|≤∑ k,bound k := by
    simp only [p,map_sum,map_smul,smul_eq_mul]
    calc
      _ ≤ ∑ k : Fin degree,|t^(k:ℕ)*L (center k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul,abs_pow]
        have hpow : |t|^(k:ℕ)≤1 := pow_le_one₀ (abs_nonneg _) ht
        exact (mul_le_mul hpow (hc k) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsplit : L r=L p+L (r-p) := by rw [map_sub]; ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hp he)

/-- Final entrywise interface consumed by the four floor checks. -/
theorem entryMajorant_sound {n inputs degree S : ℕ} (J : FactorData)
    (D : Fin n → Fin n → (Fin inputs → ℝ) →ₗ[ℝ] ℝ)
    (r : Fin inputs → ℝ) (center : Fin degree → Fin inputs → ℝ)
    (error : ℕ → ℕ) (column : ℕ → ℕ → ℕ → ℕ)
    (centerBound : ℕ → ℕ → ℕ → ℕ) (t : ℝ) (ht : |t|≤1)
    (hr : ∀ j,|r j-∑ k : Fin degree,center k j*t^(k:ℕ)|≤(error j:ℝ)/2^S)
    (hcol : ∀ u v j,|D u v (unitVector inputs j)|≤(column u v j:ℝ)/2^S)
    (hcenter : ∀ (k : Fin degree) (i j : Fin n),
      |((J.matrix n)*(Matrix.of (fun u v => D u v (center k)))*(J.matrix n).transpose) i j|≤
        (centerBound k i j:ℝ)/2^S) :
    ∀ i j : Fin n,
      |((J.matrix n)*(Matrix.of (fun u v => D u v r))*(J.matrix n).transpose) i j|≤
        (entryMajorant S n inputs degree J centerBound error column i j:ℝ)/2^S := by
  intro i j
  let p : Fin inputs → ℝ := ∑ k : Fin degree,t^(k:ℕ) • center k
  have hrem : ∀ j,|(r-p) j|≤(error j:ℝ)/2^S := by
    intro j
    simpa only [p,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hr j
  have hE : ∀ u v,|D u v (r-p)|≤
      (errorNumerator inputs error column u v:ℝ)/(2^S*2^S) :=
    fun u v => errorNumerator_bound (D u v) (r-p) error column u v hrem (hcol u v)
  have he := congruence_error_bound J (fun u v => D u v (r-p)) error column hE i j
  have h := polynomial_remainder_bound (normalizedMap (J.matrix n) D i j) r center
    (fun k => (centerBound k i j:ℝ)/2^S) t
    ((ceilShift (S+2*J.bits) (congruenceErrorNumerator n inputs J error column i j):ℝ)/2^S)
    ht (by
      rw [normalizedMap_apply]
      have heq : Matrix.of (fun u v => D u v (r-p)) = (fun u v => D u v (r-p)) := by ext u v; rfl
      rw [show Matrix.of (fun u v => D u v (r-∑ k : Fin degree,t^(k:ℕ) • center k)) =
        (fun u v => D u v (r-p)) from heq]
      exact he)
    (fun k => by simpa only [normalizedMap_apply] using hcenter k i j)
  rw [normalizedMap_apply] at h
  refine h.trans_eq ?_
  change (∑ k : Fin degree, (centerBound k i j:ℝ)/2^S)+_ =
    ((sumNat degree (fun k => centerBound k i j) +
      ceilShift (S+2*J.bits) (congruenceErrorNumerator n inputs J error column i j):ℕ):ℝ)/2^S
  rw [Nat.cast_add,add_div,sumNat_cast,Finset.sum_div]

#print axioms entryMajorant_sound
end ThomsonNegative.Certificate.Correction
