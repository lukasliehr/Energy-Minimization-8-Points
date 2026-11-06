import AllS.Units.N_GI.N_disphenoid.N_acute_triangle

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem positive_circumcenter_acute_inner (T : Fin 3 → Point) (O : Point)
    (hT : AffineIndependent ℝ T) (w : Fin 3 → ℝ) (hwpos : ∀i,0<w i)
    (hwsum : ∑i,w i=1) (hwrepr : ∑i,w i • T i=O)
    (hnorm : ∀i,‖T i-O‖^2=‖T 0-O‖^2)
    (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    0 < inner ℝ (T i-T j) (T k-T j) := by
  let f : Fin 3 → Fin 3 := ![j,i,k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  have hs : ∑l,w (e l)=1 := (e.sum_comp w).trans hwsum
  have hr : ∑l,w (e l) • T (e l)=O := (e.sum_comp (fun l => w l • T l)).trans hwrepr
  have hh := positive_circumcenter_acute_inner_zero (T ∘ e) O
    (AffineIndependent.comp_embedding e.toEmbedding hT) (w ∘ e) (hwpos (e 0)) hs hr
    (fun l => (hnorm (e l)).trans (hnorm (e 0)).symm)
  change 0 < inner ℝ (T i-T j) (T k-T j) at hh
  exact hh

theorem point_angle_acute_of_inner_pos (x y z : Point)
    (h : 0 < inner ℝ (x-y) (z-y)) : EuclideanGeometry.angle x y z<Real.pi/2 := by
  change Real.arccos (inner ℝ (x-y) (z-y)/(‖x-y‖*‖z-y‖))<Real.pi/2
  apply Real.arccos_lt_pi_div_two.mpr
  have hx : x-y≠0 := by intro hh;rw [hh,inner_zero_left] at h;exact lt_irrefl _ h
  have hz : z-y≠0 := by intro hh;rw [hh,inner_zero_right] at h;exact lt_irrefl _ h
  exact div_pos h (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hz))

theorem positive_circumcenter_acuteAngled (t : Affine.Triangle ℝ Point) (O : Point)
    (w : Fin 3 → ℝ) (hwpos : ∀i,0<w i) (hwsum : ∑i,w i=1)
    (hwrepr : ∑i,w i • t.points i=O)
    (hnorm : ∀i,‖t.points i-O‖^2=‖t.points 0-O‖^2) : t.AcuteAngled := by
  intro i j k hij hik hjk
  exact point_angle_acute_of_inner_pos _ _ _
    (positive_circumcenter_acute_inner t.points O t.independent w hwpos hwsum hwrepr hnorm i j k hij hik hjk)

#print axioms positive_circumcenter_acute_inner
#print axioms positive_circumcenter_acuteAngled
end Blueprint.Thomson.Tail.Implementation
