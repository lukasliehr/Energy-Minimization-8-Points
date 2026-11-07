import AllS.Units.N_F.N_root_contraction

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem root_fixedpoint_gain (q P v δ : ℝ) (m : ℕ) (hm : 1 ≤ m) (hmq : (m:ℝ) ≤ q)
    (hP : P ∈ Set.Icc 0 rootC) (hv : v ∈ Set.Icc 0 rootC)
    (hfix : rootT q v=v) (hres : |P-rootT q P| ≤ δ) :
    |P-v| ≤ δ/(1-rootLambda m) := by
  have hl := rootT_lipschitz q P v m hm hmq hP hv
  have h : |P-v| ≤ δ+rootLambda m*|P-v| := by
    calc
      _ = |(P-rootT q P)+(rootT q P-rootT q v)| := by rw [hfix]; congr 1; ring
      _ ≤ |P-rootT q P|+|rootT q P-rootT q v| := abs_add_le _ _
      _ ≤ _ := add_le_add hres hl
  apply (le_div_iff₀ (show 0 < 1-rootLambda m by linarith [(rootLambda_bounds m).2])).mpr
  nlinarith

theorem root_defect_fixedpoint_gain (q q₀ P v δ : ℝ) (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hP : P ∈ Set.Icc 0 rootC) (hv : v ∈ Set.Icc 0 rootC)
    (hfix : rootT q v=v) (hres : |P-rootT q P| ≤ δ) :
    |P-v| ≤ δ/(1-rootLambda ⌊q₀⌋₊) :=
  root_fixedpoint_gain q P v δ ⌊q₀⌋₊ (Nat.le_floor (by simpa using hq₀))
    ((Nat.floor_le (by linarith : 0 ≤ q₀)).trans hq) hP hv hfix hres

#check root_defect_fixedpoint_gain
#print axioms root_defect_fixedpoint_gain
end Blueprint.Thomson.Finite
