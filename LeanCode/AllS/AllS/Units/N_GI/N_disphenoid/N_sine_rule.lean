import AllS.Units.N_GI.N_disphenoid.N_acute_equal_circumradius

set_option maxHeartbeats 900000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def edgePrincipalAngle (R : ℝ) (x y : Point) : ℝ := Real.arcsin (dist x y/(2*R))

theorem edgePrincipalAngle_comm (R : ℝ) (x y : Point) :
    edgePrincipalAngle R x y=edgePrincipalAngle R y x := by simp only [edgePrincipalAngle,dist_comm]

theorem acute_triangle_edge_angle (t : Affine.Triangle ℝ Point) (ht : t.AcuteAngled)
    (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    edgePrincipalAngle t.circumradius (t.points i) (t.points k)=
      EuclideanGeometry.angle (t.points i) (t.points j) (t.points k) := by
  have hR := t.circumradius_pos
  have hs := t.dist_div_sin_angle_eq_two_mul_circumradius hij hik hjk
  have hn : Real.sin (EuclideanGeometry.angle (t.points i) (t.points j) (t.points k))≠0 := by
    intro he;rw [he,div_zero] at hs;nlinarith
  have hd := (div_eq_iff hn).mp hs
  have he : dist (t.points i) (t.points k)/(2*t.circumradius)=
      Real.sin (EuclideanGeometry.angle (t.points i) (t.points j) (t.points k)) := by
    apply (div_eq_iff (by positivity : 2*t.circumradius≠0)).mpr
    nlinarith [hd]
  rw [edgePrincipalAngle,he]
  apply Real.arcsin_sin
  · linarith [EuclideanGeometry.angle_nonneg (t.points i) (t.points j) (t.points k),Real.pi_pos]
  · exact (ht i j k hij hik hjk).le

theorem acute_triangle_edge_length (t : Affine.Triangle ℝ Point) (ht : t.AcuteAngled)
    (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    dist (t.points i) (t.points k)=2*t.circumradius*
      Real.sin (edgePrincipalAngle t.circumradius (t.points i) (t.points k)) := by
  rw [acute_triangle_edge_angle t ht i j k hij hik hjk]
  have hs := t.dist_div_sin_angle_eq_two_mul_circumradius hij hik hjk
  have hn : Real.sin (EuclideanGeometry.angle (t.points i) (t.points j) (t.points k))≠0 := by
    intro he;rw [he,div_zero] at hs;nlinarith [t.circumradius_pos]
  exact (div_eq_iff hn).mp hs

theorem acute_triangle_principal_sum (t : Affine.Triangle ℝ Point) (ht : t.AcuteAngled) :
    edgePrincipalAngle t.circumradius (t.points 0) (t.points 1)+
    edgePrincipalAngle t.circumradius (t.points 0) (t.points 2)+
    edgePrincipalAngle t.circumradius (t.points 1) (t.points 2)=Real.pi := by
  have hh := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (t.points 2)
    (t.independent.injective.ne (by decide : (1 : Fin 3)≠0))
  rw [←acute_triangle_edge_angle t ht 0 1 2 (by decide) (by decide) (by decide),
      ←acute_triangle_edge_angle t ht 1 2 0 (by decide) (by decide) (by decide),
      ←acute_triangle_edge_angle t ht 2 0 1 (by decide) (by decide) (by decide),
      edgePrincipalAngle_comm _ (t.points 1) (t.points 0),
      edgePrincipalAngle_comm _ (t.points 2) (t.points 1)] at hh
  linarith

#print axioms acute_triangle_edge_angle
#print axioms acute_triangle_principal_sum
end Blueprint.Thomson.Tail.Implementation
