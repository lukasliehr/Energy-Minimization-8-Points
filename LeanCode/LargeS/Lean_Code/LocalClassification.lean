import Lean_Code.ChartStationarity
import Lean_Code.ParameterLimit
import Lean_Code.CriticalPoint

open Real
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Local uniqueness on a fixed orbit neighborhood, with a threshold depending
only on that neighborhood.  This combines the quantitative packing loss,
stationarity, and strict convexity of the actual pair energy. -/
theorem eventual_local_sublevel_classification_proved :
    ∃ U : Set SphereTuple, IsOpen U ∧ OrbitNeighborhood U ∧
      ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
        ∀ Y : Fin 8 → ℝ³, ∀ hY : IsConfiguration Y,
          toSphereTuple Y hY.1 ∈ U → E (2 * p) Y ≤ E (2 * p) P →
            E (2 * p) Y ≥ E (2 * p) (X (aStar (2 * p))) ∧
            (E (2 * p) Y = E (2 * p) (X (aStar (2 * p))) ↔
              Congruent Y (X (aStar (2 * p)))) := by
  obtain ⟨K, ε₁, hK, hε₁, hloss⟩ := chart_sublevel_localization
  obtain ⟨ε₂, hε₂, hstationary⟩ := chart_stationarity_near_zero
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  obtain ⟨U, hUopen, hUorbit, hcover⟩ := chart_orbit_neighborhood ε hε
  obtain ⟨p₁, hp₁, hrep⟩ := optimized_chart_representation ε hε
  obtain ⟨p₂, hp₂, hconv⟩ := chartEnergy_eventually_strictConvex K hK
  obtain ⟨p₃, hp₃, hregular⟩ := chartEnergy_eventually_regular K hK
  refine ⟨U, hUopen, hUorbit, max p₁ (max p₂ p₃),
    hp₁.trans_le (le_max_left _ _), ?_⟩
  intro p hp Y hY hYU hsub
  have hpp₁ : p₁ ≤ p := (le_max_left _ _).trans hp
  have hpp₂ : p₂ ≤ p := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hpp₃ : p₃ ≤ p := (le_max_right _ _).trans ((le_max_right _ _).trans hp)
  have hppos : 0 < p := hp₁.trans_le hpp₁
  have hspos : 0 < 2 * p := by positivity
  have hastar := aStar_spec (2 * p) hspos.le
  obtain ⟨q₀, hq₀g, hq₀small, hq₀cong⟩ := hrep p hpp₁
  have hq₀config := congruent_isConfiguration hq₀cong (X_isConfiguration _ hastar.1)
  have hq₀energy : E (2 * p) (coordinateChart q₀) = E (2 * p) (X (aStar (2 * p))) :=
    congruent_energy hq₀cong
  have hq₀sub : E (2 * p) (coordinateChart q₀) ≤ E (2 * p) P := by
    rw [hq₀energy]
    exact antiprism_sublevel _ hspos
  have hq₀norm := hloss p hppos q₀ hq₀g
    (hq₀small.trans_le (min_le_left _ _)) hq₀config hq₀sub
  have hballbound : K / p ≤ 2 * K / p := by
    apply div_le_div_of_nonneg_right _ hppos.le
    linarith
  have hq₀ball : q₀ ∈ GaugeBall (2 * K / p) := ⟨hq₀g, hq₀norm.le.trans hballbound⟩
  have hq₀zero := hstationary p _ hastar.1 hastar.2 q₀
    (hq₀small.trans_le (min_le_right _ _)) (congruent_symm hq₀cong)
  have hmin := strictConvex_stationary_minimum _ _ (hconv p hpp₂) q₀ hq₀ball
    ((hregular p hpp₃ q₀ hq₀ball.2).1.differentiableAt (by norm_num)) hq₀zero
  obtain ⟨q, hqg, hqsmall, hqcong⟩ := hcover (toSphereTuple Y hY.1) hYU
  change Congruent Y (coordinateChart q) at hqcong
  have hqconfig := congruent_isConfiguration hqcong hY
  have hqenergy : E (2 * p) (coordinateChart q) = E (2 * p) Y := congruent_energy hqcong
  have hqsub : E (2 * p) (coordinateChart q) ≤ E (2 * p) P := by
    rw [hqenergy]
    exact hsub
  have hqnorm := hloss p hppos q hqg
    (hqsmall.trans_le (min_le_left _ _)) hqconfig hqsub
  have hqball : q ∈ GaugeBall (2 * K / p) := ⟨hqg, hqnorm.le.trans hballbound⟩
  have hm := hmin q hqball
  rw [chartEnergy_eq, chartEnergy_eq, hq₀energy, hqenergy] at hm
  refine ⟨hm.1, ?_⟩
  constructor
  · intro heq
    have hqq := hm.2.mp heq
    rw [hqq] at hqcong
    exact congruent_trans hqcong (congruent_symm hq₀cong)
  · intro hc
    exact (congruent_energy hc).symm

end SquareAntiprismVerification
