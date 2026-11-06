import ThomsonNegative.Compact.Target.Table
import ThomsonNegative.Analytic.ScalarReduction

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed

variable {N S B W : ℕ}

theorem radd_eok (hg : Good N S B W) {A B' : TM} {f g : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (hB : EOK (mkCtx N S B W) B' g) :
    EOK (mkCtx N S B W) (radd (mkCtx N S B W) A B') (fun t => f t+g t) :=
  refresh_eok hg (add_eok hA hB rfl)

theorem rmul_eok (hg : Good N S B W) {A B' : TM} {f g : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (hB : EOK (mkCtx N S B W) B' g) :
    EOK (mkCtx N S B W) (rmul (mkCtx N S B W) A B') (fun t => f t*g t) :=
  refresh_eok hg (mul_eok hg hA hB)

theorem smul_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (ng : Bool) (mag err : ℕ) (z : ℝ)
    (hz : |z-(if ng then -(mag:ℝ) else mag)/2^S| ≤ (err:ℝ)/2^S) :
    EOK (mkCtx N S B W) (smul (mkCtx N S B W) ng mag err A) (fun t => z*f t) := by
  intro hok
  exact smul_sound hg (hA (smul_ok hok)) ng mag err z hz hok

theorem rdiv_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (n : ℕ) :
    EOK (mkCtx N S B W) (rdiv (mkCtx N S B W) A n) (fun t => f t/n) := by
  have he := ratMag_err (N:=N) (S:=S) (B:=B) (W:=W) (false,1,n)
  simp only [qval, Bool.false_eq_true, ↓reduceIte, Nat.cast_one] at he
  exact (refresh_eok hg (smul_eok hg hA false (ratMag (mkCtx N S B W) 1 n) 1 (1/n)
    (by simpa using he))).congr (fun t _ => by ring)

theorem addNat_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (n : ℕ) :
    EOK (mkCtx N S B W) (addNat (mkCtx N S B W) A n) (fun t => f t+n) := by
  intro hok
  have hκ : |(n:ℝ)-((n*2^S:ℕ):ℝ)/2^S| ≤ (0:ℝ)/2^S := by
    push_cast
    simp
  exact addC_sound (hA (addC_ok hok)) false (n*2^S) 0 n (by simpa using hκ) hok hg

theorem half_scalar (hS : 1 ≤ S) : ((2^(S-1):ℕ):ℝ)/2^S = (1:ℝ)/2 := by
  norm_cast
  push_cast
  have he : S=(S-1)+1 := by omega
  conv_lhs => rw [he]
  rw [show S-1+1-1=S-1 by omega,pow_succ]
  field_simp

theorem half_eok (hg : Good N S B W) (hS : 1 ≤ S) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) :
    EOK (mkCtx N S B W) (half (mkCtx N S B W) A) (fun t => f t/2) := by
  have he : |(1:ℝ)/2-((2^(S-1):ℕ):ℝ)/2^S| ≤ (0:ℝ)/2^S := by
    rw [half_scalar hS]; simp
  exact (refresh_eok hg (smul_eok hg hA false (2^(S-1)) 0 (1/2)
    (by simpa using he))).congr (fun t _ => by ring)

/-- Both accumulated partial sums and the next slope term share one recurrence. -/
theorem seriesEvaluate_eok (hg : Good N S B W) {Q X : TM} {q x : ℝ → ℝ}
    (hq : EOK (mkCtx N S B W) Q q) (hx : EOK (mkCtx N S B W) X x) (n : ℕ) :
    EOK (mkCtx N S B W) (seriesEvaluate (mkCtx N S B W) Q X n).term
      (fun t => slopeCoeff (q t) n*(x t)^(n+1)) ∧
    EOK (mkCtx N S B W) (seriesEvaluate (mkCtx N S B W) Q X n).value
      (fun t => auxPartial (q t) (x t) n) ∧
    EOK (mkCtx N S B W) (seriesEvaluate (mkCtx N S B W) Q X n).slope
      (fun t => slopePartial (q t) (x t) n) := by
  induction n with
  | zero =>
    refine ⟨?_,?_,?_⟩
    · simpa [seriesEvaluate,slopeCoeff,seriesCoeff] using hx
    · exact (EOK.of_encl zero_sound).congr (fun t _ => by simp [auxPartial])
    · exact (EOK.of_encl zero_sound).congr (fun t _ => by simp [slopePartial])
  | succ n ih =>
    let U := rdiv (mkCtx N S B W)
      (rmul (mkCtx N S B W) (seriesEvaluate (mkCtx N S B W) Q X n).term X) (n+2)
    have hu : EOK (mkCtx N S B W) U (fun t => seriesCoeff (q t) n*(x t)^(n+2)) := by
      apply (rdiv_eok hg (rmul_eok hg ih.1 hx) (n+2)).congr
      intro t _
      unfold slopeCoeff
      push_cast
      rw [show n+2=n+1+1 by omega,pow_succ]
      have hn : (n:ℝ)+2 ≠ 0 := by positivity
      field_simp [hn]
      simp only [pow_succ]
      ring
    refine ⟨?_,?_,?_⟩
    · apply (rmul_eok hg hu (addNat_eok hg hq (n+1))).congr
      intro t _
      simp only [slopeCoeff,seriesCoeff,Nat.cast_add,Nat.cast_one]
      have hn : (n:ℝ)+3 ≠ 0 := by positivity
      field_simp [hn]
      ring
    · apply (radd_eok hg ih.2.1 hu).congr
      intro t _
      simp only [auxPartial,Finset.sum_range_succ]
    · apply (radd_eok hg ih.2.2 ih.1).congr
      intro t _
      simp only [slopePartial,Finset.sum_range_succ]

theorem scaled_divUp_bound (a d s : ℕ) (hd : 0 < d) (hs : 0 < s) :
    (a:ℝ)/d ≤ (divUp (s*a) d:ℝ)/s := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have h := le_ceil_div (s*a) d hd
  change ((s*a:ℕ):ℝ)/d ≤ (divUp (s*a) d:ℝ) at h
  have h' := (div_le_iff₀ hd').mp h
  apply (div_le_div_iff₀ hd' hs').2
  push_cast at h'
  nlinarith

theorem slopeTail_bound (n rnum rden : ℕ) (hr : rnum < rden) :
    ((rnum:ℝ)/rden)^(n+1)/(1-(rnum:ℝ)/rden) ≤
      (slopeTail (mkCtx N S B W) n rnum rden:ℝ)/2^S := by
  have hd : 0 < rden := by omega
  have he : 0 < rden-rnum := by omega
  have hd' : (rden:ℝ) ≠ 0 := by positivity
  have he' : (rden:ℝ)-(rnum:ℝ) ≠ 0 := by
    have h : (rnum:ℝ)<rden := by exact_mod_cast hr
    linarith
  have h := scaled_divUp_bound (rnum^(n+1)) (rden^n*(rden-rnum)) (2^S)
    (by positivity) (by positivity)
  simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_sub hr.le,Nat.cast_ofNat] at h
  change _ ≤ (slopeTail (mkCtx N S B W) n rnum rden:ℝ)/2^S at h
  convert h using 1
  push_cast [Nat.cast_sub hr.le]
  rw [div_pow]
  field_simp [hd',he']
  rw [pow_succ]
  ring

theorem valueTail_bound (n rnum rden : ℕ) (hr : rnum < rden) :
    ((rnum:ℝ)/rden)^(n+2)/((n+2)*(1-(rnum:ℝ)/rden)) ≤
      (valueTail (mkCtx N S B W) n rnum rden:ℝ)/2^S := by
  have hd : 0 < rden := by omega
  have he : 0 < rden-rnum := by omega
  have hd' : (rden:ℝ) ≠ 0 := by positivity
  have he' : (rden:ℝ)-(rnum:ℝ) ≠ 0 := by
    have h : (rnum:ℝ)<rden := by exact_mod_cast hr
    linarith
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  have h := scaled_divUp_bound (rnum^(n+2)) ((n+2)*rden^(n+1)*(rden-rnum)) (2^S)
    (by positivity) (by positivity)
  simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_sub hr.le,Nat.cast_add,Nat.cast_ofNat] at h
  change _ ≤ (valueTail (mkCtx N S B W) n rnum rden:ℝ)/2^S at h
  convert h using 1
  push_cast [Nat.cast_sub hr.le]
  rw [div_pow]
  field_simp [hd',he',hn]
  simp only [pow_succ]
  ring

theorem positivePair_eok (hg : Good N S B W) {Q X : TM} {q x : ℝ → ℝ}
    (hq : EOK (mkCtx N S B W) Q q) (hx : EOK (mkCtx N S B W) X x)
    (n rnum rden : ℕ) (hr : rnum < rden)
    (hqdom : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (hxdom : ∀ t ∈ Set.Icc (-1:ℝ) 1, x t ∈ Set.Icc (0:ℝ) ((rnum:ℝ)/rden)) :
    EOK (mkCtx N S B W) (positivePair (mkCtx N S B W) Q X n rnum rden).value
      (fun t => auxSeries (q t) (x t)) ∧
    EOK (mkCtx N S B W) (positivePair (mkCtx N S B W) Q X n rnum rden).slope
      (fun t => slopeSeries (q t) (x t)) := by
  have hd : (0:ℝ)<rden := by exact_mod_cast (show 0<rden by omega)
  have hρ : (rnum:ℝ)/rden < 1 := (div_lt_one hd).2 (by exact_mod_cast hr)
  have hpart := seriesEvaluate_eok hg hq hx n
  constructor
  · intro hok
    have hbase : (seriesEvaluate (mkCtx N S B W) Q X n).value.ok = true := by
      change ((seriesEvaluate (mkCtx N S B W) Q X n).value.ok && Nat.blt rnum rden) = true at hok
      simp only [Bool.and_eq_true] at hok
      exact hok.1
    have hv := widen_sound (valueTail (mkCtx N S B W) n rnum rden) (hpart.2.1 hbase)
      (g:=fun t => auxSeries (q t) (x t)) (by
        intro t ht
        have htX := hxdom t ht
        have hx1 : x t < 1 := htX.2.trans_lt hρ
        have hs := auxSeries_tail (q t) (x t) (hqdom t ht) ⟨htX.1,hx1⟩ n
        rw [abs_of_nonneg hs.1]
        refine hs.2.trans ((?_ : (x t)^(n+2)/((n+2)*(1-x t)) ≤
            ((rnum:ℝ)/rden)^(n+2)/((n+2)*(1-(rnum:ℝ)/rden))).trans
          (valueTail_bound (N:=N) (S:=S) (B:=B) (W:=W) n rnum rden hr))
        gcongr <;> linarith [htX.1,htX.2])
    exact hv.of_fields rfl rfl rfl rfl
  · intro hok
    have hbase : (seriesEvaluate (mkCtx N S B W) Q X n).slope.ok = true := by
      change ((seriesEvaluate (mkCtx N S B W) Q X n).slope.ok && Nat.blt rnum rden) = true at hok
      simp only [Bool.and_eq_true] at hok
      exact hok.1
    have hv := widen_sound (slopeTail (mkCtx N S B W) n rnum rden) (hpart.2.2 hbase)
      (g:=fun t => slopeSeries (q t) (x t)) (by
        intro t ht
        have htX := hxdom t ht
        have hx1 : x t < 1 := htX.2.trans_lt hρ
        have hs := slopeSeries_tail (q t) (x t) (hqdom t ht) ⟨htX.1,hx1⟩ n
        rw [abs_of_nonneg hs.1]
        refine hs.2.trans ((?_ : (x t)^(n+1)/(1-x t) ≤
            ((rnum:ℝ)/rden)^(n+1)/(1-(rnum:ℝ)/rden)).trans
          (slopeTail_bound (N:=N) (S:=S) (B:=B) (W:=W) n rnum rden hr))
        gcongr <;> linarith [htX.1,htX.2])
    exact hv.of_fields rfl rfl rfl rfl

#print axioms seriesEvaluate_eok
#print axioms positivePair_eok
end ThomsonNegative.Compact.Target
