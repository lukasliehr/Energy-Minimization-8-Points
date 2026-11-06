import AllS.Units.N_AI.N_scalar_models.N_log_common_hull

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def coefficientVariation {n : ℕ} (a : Fin (n+1)→ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase (0:Fin (n+1)), |a k|

def ScalarSegmentVariationStatement : Prop :=
  ∀ {n : ℕ} (a : Fin (n+1)→ℝ) (x u : ℝ),
    x∈cellDomain → u∈Set.uIcc 0 x →
    |scalarEval a x-scalarEval a u| ≤ coefficientVariation a ∧
    |scalarEval a x-a 0| ≤ coefficientVariation a

theorem abs_pow_sub_pow_le_one_of_segment (x u : ℝ) (k : ℕ)
    (hx : x∈cellDomain) (hu : u∈Set.uIcc 0 x) : |x^k-u^k|≤1 := by
  rw [← segment_eq_uIcc] at hu
  rcases hu with ⟨r,t,hr,ht,hrt,hu⟩
  have ht₁ : t≤1 := by linarith
  have hut : t*x=u := by simpa using hu
  have htp₀ : 0≤t^k := pow_nonneg ht _
  have htp₁ : t^k≤1 := pow_le_one₀ ht ht₁
  have hxp₁ : |x|^k≤1 := pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
  rw [← hut]
  calc
    |x^k-(t*x)^k| = |x|^k*|1-t^k| := by
      rw [mul_pow, ← abs_pow, ← abs_mul]
      congr 1
      ring
    _ = |x|^k*(1-t^k) := by rw [abs_of_nonneg (sub_nonneg.mpr htp₁)]
    _ ≤ 1*1 := mul_le_mul hxp₁ (by linarith) (by linarith) zero_le_one
    _ = 1 := one_mul _

theorem scalarEval_segment_bound {n : ℕ} (a : Fin (n+1)→ℝ) (x u : ℝ)
    (hx : x∈cellDomain) (hu : u∈Set.uIcc 0 x) :
    |scalarEval a x-scalarEval a u| ≤ coefficientVariation a := by
  have hid : scalarEval a x-scalarEval a u =
      ∑ k ∈ Finset.univ.erase (0:Fin (n+1)), a k*(x^k.val-u^k.val) := by
    rw [scalarEval_split_zero a x, scalarEval_split_zero a u]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_one_of_segment x u k.val hx hu)
    (abs_nonneg (a k))).trans_eq (mul_one _)

theorem scalarEval_at_zero {n : ℕ} (a : Fin (n+1)→ℝ) : scalarEval a 0 = a 0 := by
  rw [scalarEval_split_zero]
  have hz : ∑ k ∈ Finset.univ.erase (0:Fin (n+1)), a k*(0:ℝ)^k.val = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk₀ : k.val≠0 := by
      intro he
      exact (Finset.mem_erase.mp hk).1 (Fin.ext he)
    simp [hk₀]
  rw [hz, add_zero]

theorem scalar_models_segment_variation : ScalarSegmentVariationStatement := by
  intro n a x u hx hu
  refine ⟨scalarEval_segment_bound a x u hx hu, ?_⟩
  simpa only [scalarEval_at_zero] using
    scalarEval_segment_bound a x 0 hx (Set.left_mem_uIcc)

#check scalar_models_segment_variation
#print ScalarSegmentVariationStatement
#print axioms scalar_models_segment_variation
end Blueprint.CAP
