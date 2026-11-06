import ThomsonNegative.Certificate.Correction.CongruenceKernel
import ThomsonNegative.Certificate.MatrixSound
import ThomsonNegative.Certificate.MetricSound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

lemma allOk_entry (A : TMMatrix) (h : allOk A=true) (i j : ℕ) :
    (entry A i j).ok=true := by
  have hall := List.all_eq_true.mp h
  by_cases hi : i<A.length
  · have hrow := hall _ (List.getElem_mem hi)
    by_cases hj : j<(A[i]).length
    · have hh := List.all_eq_true.mp hrow _ (List.getElem_mem hj)
      simpa only [entry,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hj,Option.getD_some] using hh
    · simp [entry,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hj),zeroTM]
  · simp [entry,List.getD_eq_getElem?_getD,
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi),zeroTM]

variable {N S B W : ℕ}

theorem metricTM_sound (hg : Good N S B W) (n : ℕ) (J : FactorData)
    (hok : allOk (metricTM (mkCtx N S B W) n J)=true) :
    ∀ i : Fin n, ∀ j : Fin n,
      Encl (mkCtx N S B W) (entry (metricTM (mkCtx N S B W) n J) i j)
        (fun _ => J.matrix n i j) := by
  intro i j
  have he := entry_tabulate
    (fun i j => rationalTM (mkCtx N S B W)
      (differenceArg (factorEntry J i j) (Nat.pow 2 J.bits))) i.isLt j.isLt
  rw [show entry (metricTM (mkCtx N S B W) n J) i j = _ from he]
  have h := rationalTM_sound hg _ (by rw [← he]; exact allOk_entry _ hok i j)
  apply h.congr
  intro t ht
  rw [differenceArg_val]
  simp only [FactorData.matrix,FactorData.eval,Nat.cast_pow,Nat.cast_ofNat,Nat.pow_eq]

theorem congruenceTM_sound (hg : Good N S B W) (n : ℕ) (J : FactorData)
    (M : TMMatrix) (m : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hm : ∀ i j : Fin n, Encl (mkCtx N S B W) (entry M i j) (fun t => m t i j))
    (hok : congruenceGate (mkCtx N S B W) n J M=true) :
    ∀ i j : Fin n, Encl (mkCtx N S B W)
      (entry (congruenceTM (mkCtx N S B W) n J M) i j)
      (fun t => (J.matrix n * m t * (J.matrix n).transpose) i j) := by
  simp only [congruenceGate,Bool.and_eq_true] at hok
  let Z := metricTM (mkCtx N S B W) n J
  let a : ℕ → ℕ → ℝ → ℝ := fun i j _ => J.eval i j
  let b : ℕ → ℕ → ℝ → ℝ := fun i j t =>
    if hi : i<n then if hj : j<n then m t ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0
  have hZ := metricTM_sound hg n J hok.1.1.1
  have hb : ∀ i<n,∀ j<n,Encl (mkCtx N S B W) (entry M i j) (b i j) := by
    intro i hi j hj
    simpa only [b,dif_pos hi,dif_pos hj] using hm ⟨i,hi⟩ ⟨j,hj⟩
  have hleft := matmulTM_sound hg n n n Z M a b
    (fun i hi j hj => hZ ⟨i,hi⟩ ⟨j,hj⟩) hb
    (fun i _ j _ => allOk_entry _ hok.1.2 i j)
  have hright := matmulTM_sound hg n n n
    (matmulTM (mkCtx N S B W) n n n Z M) (transposeTM n n Z)
    (fun i j t => ∑ k ∈ Finset.range n,a i k t*b k j t)
    (fun i j t => a j i t) hleft
    (by
      intro i hi j hj
      rw [show entry (transposeTM n n Z) i j=entry Z j i from entry_tabulate _ hi hj]
      exact hZ ⟨j,hj⟩ ⟨i,hi⟩)
    (fun i _ j _ => allOk_entry _ hok.2 i j)
  intro i j
  apply (hright i i.isLt j j.isLt).congr
  intro t ht
  simp only [Matrix.mul_apply,Matrix.transpose_apply,FactorData.matrix,a,b]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [dif_pos k.isLt]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  simp only [dif_pos u.isLt]

#print axioms congruenceTM_sound
end ThomsonNegative.Certificate.Correction
