import AllS.Units.N_FI.N_rolle_multiset.N_derivative_zeros

noncomputable section
namespace Blueprint.Thomson.Finite

theorem rolle_multiset_induction (N : ℕ) (f : ℕ → ℝ → ℝ) (l u : ℝ)
    (htower : DerivativeTowerOn f N l u) (z : Fin (N+1) → ℝ)
    (hmono : Monotone z) (hmem : ∀ i, z i ∈ Set.Icc l u) (hzero : JetZeroList f z) :
    ∃ ξ ∈ Set.Icc l u, f N ξ=0 := by
  induction N generalizing f with
  | zero => exact ⟨z 0,hmem 0,hzero.value 0⟩
  | succ N ih =>
    obtain ⟨w,hwmono,hwmem,hwzero⟩ := rolle_multiset_derivative_zeros N f l u
      (htower.continuous 0 (by omega)) (htower.derivative 0 (by omega)) z hmono hmem hzero
    have htower' : DerivativeTowerOn (fun k => f (k+1)) N l u := by
      constructor
      · intro k hk
        exact htower.continuous (k+1) (by omega)
      · intro k hk x hx
        exact htower.derivative (k+1) (by omega) x hx
    exact ih (fun k => f (k+1)) htower' w hwmono hwmem hwzero

#check rolle_multiset_induction
#print axioms rolle_multiset_induction
end Blueprint.Thomson.Finite
