import AllS.Units.N_GI.N_nearest_chart.N_frame
import Mathlib.Topology.Order.Compact

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

/-- The same closed bounded operator model as upstream OrbitClosure, with no
unrelated eventual-large-s theorem imported. -/
def gaugeOrthogonalOperators : Set (Point →L[ℝ] Point) := {T | ∀ x, ‖T x‖=‖x‖}

abbrev gaugePermutationTopology : TopologicalSpace (Equiv.Perm (Fin 8)) := ⊥
attribute [local instance] gaugePermutationTopology
local instance : DiscreteTopology (Equiv.Perm (Fin 8)) := ⟨rfl⟩

abbrev GaugeAction := (Point →L[ℝ] Point) × Equiv.Perm (Fin 8)
def gaugeActions : Set GaugeAction := gaugeOrthogonalOperators ×ˢ Set.univ

def gaugeOrthogonalEquiv (T : Point →L[ℝ] Point) (hT : T∈gaugeOrthogonalOperators) :
    Point ≃ₗᵢ[ℝ] Point :=
  let f : Point →ₗᵢ[ℝ] Point := {toLinearMap := T.toLinearMap,norm_map' := hT}
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective (f := f.toLinearMap) f.injective)

@[simp] theorem gaugeOrthogonalEquiv_apply (T : Point →L[ℝ] Point)
    (hT : T∈gaugeOrthogonalOperators) (x : Point) : gaugeOrthogonalEquiv T hT x=T x := rfl

theorem gaugeOrthogonalOperators_isClosed : IsClosed gaugeOrthogonalOperators := by
  have he : gaugeOrthogonalOperators=⋂x : Point,{T : Point →L[ℝ] Point | ‖T x‖=‖x‖} := by
    ext T; simp [gaugeOrthogonalOperators]
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_eq <;> fun_prop

theorem gaugeOrthogonalOperators_isCompact : IsCompact gaugeOrthogonalOperators := by
  apply (isCompact_closedBall (0 : Point →L[ℝ] Point) 1).of_isClosed_subset gaugeOrthogonalOperators_isClosed
  intro T hT
  rw [Metric.mem_closedBall,dist_zero_right]
  apply T.opNorm_le_bound (by norm_num)
  intro x
  rw [hT x,one_mul]

theorem product_gauge_compact_action : IsCompact gaugeActions :=
  gaugeOrthogonalOperators_isCompact.prod isCompact_univ

theorem gaugeActions_nonempty : gaugeActions.Nonempty :=
  ⟨(ContinuousLinearMap.id ℝ Point,Equiv.refl _),(fun _ => rfl),Set.mem_univ _⟩

def alignedConfiguration (Y : Fin 8 → Point) (a : GaugeAction) (i : Fin 8) : Point := a.1 (Y (a.2 i))
def gaugeProduct (Y : Fin 8 → Point) (a : GaugeAction) : ℝ :=
  ∏i,max (inner ℝ (packingReference i) (alignedConfiguration Y a i)) 0

def gaugeChordSquare (Y : Fin 8 → Point) (a : GaugeAction) : ℝ :=
  ∑i,‖alignedConfiguration Y a i-packingReference i‖^2

def productGauge (Y : Fin 8 → Point) : ℝ := sSup (gaugeProduct Y '' gaugeActions)
def chordOrbitSquare (Y : Fin 8 → Point) : ℝ := sInf (gaugeChordSquare Y '' gaugeActions)

theorem alignedConfiguration_continuous (i : Fin 8) :
    Continuous (fun p : (Fin 8 → Point) × GaugeAction => alignedConfiguration p.1 p.2 i) := by
  unfold alignedConfiguration
  apply Continuous.clm_apply
  · fun_prop
  · rw [continuous_iff_continuousAt]
    intro p
    have hc : Continuous (fun p : (Fin 8 → Point) × GaugeAction => p.2.2) := by fun_prop
    have he : ∀ᶠ z in nhds p,z.2.2=p.2.2 :=
      hc.continuousAt.eventually (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton p.2.2))
    apply ((continuous_apply (p.2.2 i)).comp continuous_fst).continuousAt.congr_of_eventuallyEq
    filter_upwards [he] with z hz
    rw [hz]
    rfl

theorem gaugeProduct_continuous :
    Continuous (fun p : (Fin 8 → Point) × GaugeAction => gaugeProduct p.1 p.2) := by
  unfold gaugeProduct
  apply continuous_finsetProd
  intro i _
  exact (continuous_const.inner (alignedConfiguration_continuous i)).max continuous_const

theorem gaugeChordSquare_continuous :
    Continuous (fun p : (Fin 8 → Point) × GaugeAction => gaugeChordSquare p.1 p.2) := by
  unfold gaugeChordSquare
  apply continuous_finsetSum
  intro i _
  exact ((alignedConfiguration_continuous i).sub continuous_const).norm.pow 2

#print axioms product_gauge_compact_action
end Blueprint.Thomson.Tail.Implementation
