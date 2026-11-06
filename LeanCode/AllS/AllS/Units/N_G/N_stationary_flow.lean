import AllS.Units.N_GI.N_stationary_flow.N_assemble

noncomputable section
open Real
namespace Blueprint.Thomson.Tail

theorem stationary_flow (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    Implementation.NonnegativeCirculation (Implementation.forceFlow p (Implementation.forceAxis Y i₀ j₀ m) Y) ∧
    Implementation.forceFlow p (Implementation.forceAxis Y i₀ j₀ m) Y i₀ j₀=
      m^(-p-1)*sin (Implementation.forceAngle m) ∧
    0<Implementation.forceFlow p (Implementation.forceAxis Y i₀ j₀ m) Y i₀ j₀ :=
  Implementation.stationary_flow_assemble Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin

#check stationary_flow
#print axioms stationary_flow
end Blueprint.Thomson.Tail
