import AllS.Units.N_GI.N_weighted_monotonicity.N_variance_derivative

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem weightedNegativeMass_ge_one {n : ℕ} (w x : Fin n → ℝ)
    (hw : ∀ i, 1 ≤ w i) (hp : 0 < weightedNegativeMass w x) : 1 ≤ weightedNegativeMass w x := by
  have hex : ∃ i, x i < 0 := by
    by_contra h
    push_neg at h
    have hz : weightedNegativeMass w x=0 := by
      unfold weightedNegativeMass
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (not_lt_of_ge (h i))
    linarith
  obtain ⟨i,hi⟩ := hex
  have hn (j : Fin n) : 0 ≤ if x j<0 then w j else 0 := by
    split_ifs
    · linarith [hw j]
    · norm_num
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hn j)
    (Finset.mem_univ i)
  rw [if_pos hi] at h
  exact le_trans (hw i) h

theorem weighted_monotonicity_mass_one {n : ℕ} (hn : 2 ≤ n) (w x : Fin n → ℝ)
    (hw : ∀ i, 1 ≤ w i) (v : ℝ) (hv : 0 < v) (hm : weightedMean w x=0)
    (hq : v^2 ≤ weightedSquare w x) :
    twoValueExp (∑ i,w i) v 1 ≤ weightedExp w x := by
  have hwp (i : Fin n) : 0 < w i := by linarith [hw i]
  let u := √(weightedSquare w x)
  have hqp : 0 < weightedSquare w x := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.mpr hqp
  have hus : u^2=weightedSquare w x := Real.sq_sqrt hqp.le
  have hvu : v ≤ u := by nlinarith
  have hx : x ∈ weightedFeasible w u := ⟨hm,hus.symm⟩
  obtain ⟨y,hy,hmin,z,hz,hzW,hzmass,hvals,hl,hh,hvalue⟩ := weighted_two_value hn w hwp u hu
  have hmass : 1 ≤ z := by
    rw [hzmass]
    exact weightedNegativeMass_ge_one w y hw (hzmass ▸ hz)
  have hW1 : 1 < ∑ i,w i := lt_of_le_of_lt hmass hzW
  have hmmono := (twoValueExp_strictMono_mass (∑ i,w i) v hv).monotoneOn
    (show (1:ℝ) ∈ Set.Ioo 0 (∑ i,w i) from ⟨by norm_num,hW1⟩)
    ⟨hz,hzW⟩ hmass
  have hvmono := (twoValueExp_strictMono_variance (∑ i,w i) z hz hzW).monotoneOn hv hu hvu
  have henergy : weightedExp w y ≤ weightedExp w x := hmin hx
  calc
    _ ≤ twoValueExp (∑ i,w i) v z := hmmono
    _ ≤ twoValueExp (∑ i,w i) u z := hvmono
    _ = weightedExp w y := hvalue.symm
    _ ≤ _ := henergy

#check weighted_monotonicity_mass_one
#print axioms weighted_monotonicity_mass_one
end Blueprint.Thomson.Tail.Implementation
