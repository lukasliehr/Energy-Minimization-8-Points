import AllS.Units.N_GI.N_stationary_flow.N_circulation

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

/-- The four explicit flow properties used by finite cycle decomposition. -/
def NonnegativeCirculation (f : Fin 8 → Fin 8 → ℝ) : Prop :=
  (∀ i j, 0 ≤ f i j) ∧ (∀ i, f i i=0) ∧
  (∀ i j, ¬(0<f i j ∧ 0<f j i)) ∧
  (∀ i, (∑ j : Fin 8, f i j)=∑ j : Fin 8, f j i)

theorem stationary_flow_assemble (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    NonnegativeCirculation (forceFlow p (forceAxis Y i₀ j₀ m) Y) ∧
    forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀=m^(-p-1)*sin (forceAngle m) ∧
    0<forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀ := by
  obtain ⟨hbalance,he,hpos⟩ := stationary_flow_circulation Y p m i₀ j₀
    hY hp hstat hne hm hmmax hd hmin
  exact ⟨⟨forceFlow_nonneg p _ Y,forceFlow_self p _ Y,forceFlow_no_opposite p _ Y,hbalance⟩,
    he,hpos⟩

#check stationary_flow_assemble
#print axioms stationary_flow_assemble
end Blueprint.Thomson.Tail.Implementation
