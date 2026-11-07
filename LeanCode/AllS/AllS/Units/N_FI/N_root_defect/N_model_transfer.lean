import AllS.Units.N_FI.N_root_defect.N_fixedpoint_gain

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem root_defect_point (s q₀ P δ : ℝ) (m : ℕ) (hs : 0 ≤ s) (hq₀ : 1 ≤ q₀)
    (hq : q₀ ≤ 1+s/2) (hm : 1 ≤ m) (hmq₀ : (m:ℝ) ≤ q₀)
    (hP : P ∈ Set.Icc 0 rootC) (hres : |P-rootT (1+s/2) P| ≤ δ) :
    |aS s-rootHeight (1+s/2) P| ≤ 5*δ/(17*q₀*(1-rootLambda m)) := by
  obtain ⟨hv,hfix,hh⟩ := aS_root_coordinates s hs
  have hgain := root_fixedpoint_gain (1+s/2) P (rootV s) δ m hm (hmq₀.trans hq) hP hv hfix hres
  have hheight := rootHeight_lipschitz (1+s/2) q₀ (rootV s) P hq₀ hq hv hP
  rw [hh,abs_sub_comm (rootV s) P] at hheight
  calc
    _ ≤ (5/(17*q₀))*|P-rootV s| := hheight
    _ ≤ (5/(17*q₀))*(δ/(1-rootLambda m)) := mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = _ := by rw [mul_div_mul_comm]

theorem root_defect_model_transfer (s P H : ℝ → ℝ) (q₀ C δ e : ℝ)
    (hq₀ : 1 ≤ q₀) (hC : C ≤ rootC)
    (hs : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ s t)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q₀ ≤ 1+s t/2)
    (hP : ∀ t ∈ Set.Icc (-1:ℝ) 1, P t ∈ Set.Icc 0 C)
    (hres : ∀ t ∈ Set.Icc (-1:ℝ) 1, |P t-rootT (1+s t/2) (P t)| ≤ δ)
    (hmodel : ∀ t ∈ Set.Icc (-1:ℝ) 1, |H t-rootHeight (1+s t/2) (P t)| ≤ e) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1, |H t-aS (s t)| ≤ e+5*δ/(17*q₀*(1-rootLambda ⌊q₀⌋₊)) := by
  intro t ht
  have hp : P t ∈ Set.Icc 0 rootC := ⟨(hP t ht).1,(hP t ht).2.trans hC⟩
  have h := root_defect_point (s t) q₀ (P t) δ ⌊q₀⌋₊ (hs t ht) hq₀ (hq t ht)
    (Nat.le_floor (by simpa using hq₀)) (Nat.floor_le (by linarith)) hp (hres t ht)
  rw [abs_sub_comm (aS (s t))] at h
  exact (abs_sub_le (H t) (rootHeight (1+s t/2) (P t)) (aS (s t))).trans (add_le_add (hmodel t ht) h)

#check root_defect_model_transfer
#print axioms root_defect_model_transfer
#print axioms root_defect_point
end Blueprint.Thomson.Finite
