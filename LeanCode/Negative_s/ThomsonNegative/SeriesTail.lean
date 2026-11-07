import ThomsonNegative.Series

noncomputable section
open scoped BigOperators
namespace ThomsonNegative

def auxSeries (q x : ℝ) : ℝ := ∑' n, seriesCoeff q n * x^(n+2)

def auxPartial (q x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, seriesCoeff q n * x^(n+2)

lemma series_shift_term_bound (q x : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : 0 ≤ x) (N n : ℕ) :
    seriesCoeff q (n+N) * x^(n+N+2) ≤ (x^(N+2)/(N+2))*x^n := by
  have hc : seriesCoeff q (n+N) ≤ 1/(N+2) :=
    (seriesCoeff_antitone q hq (Nat.le_add_left N n)).trans
      ((le_div_iff₀ (by positivity : (0 : ℝ) < N+2)).mpr (seriesCoeff_bounds q hq N).2)
  have hp : x^(n+N+2) = x^(N+2)*x^n := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (1/(N+2))*x^(n+N+2) := mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
    _ = _ := by rw [hp]; ring

lemma auxSeries_summable (q x : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun n => seriesCoeff q n*x^(n+2)) := by
  have h := ((hasSum_geometric_of_lt_one hx.1 hx.2).mul_left (x^2/2)).summable
  apply Summable.of_nonneg_of_le (fun n => (seriesTerm_bound q x hq hx.1 n).1) _ h
  intro n
  simpa using series_shift_term_bound q x hq hx.1 0 n

/-- One uniform geometric tail for the full closed parameter interval. -/
theorem auxSeries_tail (q x : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (N : ℕ) :
    0 ≤ auxSeries q x - auxPartial q x N ∧
    auxSeries q x - auxPartial q x N ≤ x^(N+2)/((N+2)*(1-x)) := by
  have hs := auxSeries_summable q x hq hx
  have hshift : Summable (fun n => seriesCoeff q (n+N)*x^(n+N+2)) :=
    (summable_nat_add_iff N).mpr hs
  have hgeom := (hasSum_geometric_of_lt_one hx.1 hx.2).mul_left (x^(N+2)/(N+2))
  have he : auxSeries q x-auxPartial q x N =
      ∑' n, seriesCoeff q (n+N)*x^(n+N+2) := by
    have h := hs.sum_add_tsum_nat_add N
    change auxPartial q x N + _ = auxSeries q x at h
    linarith
  rw [he]
  refine ⟨tsum_nonneg (fun n => (seriesTerm_bound q x hq hx.1 (n+N)).1),?_⟩
  calc
    _ ≤ ∑' n, (x^(N+2)/(N+2))*x^n :=
      Summable.tsum_le_tsum (series_shift_term_bound q x hq hx.1 N) hshift hgeom.summable
    _ = _ := by rw [hgeom.tsum_eq]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

#print axioms auxSeries_tail
end ThomsonNegative
