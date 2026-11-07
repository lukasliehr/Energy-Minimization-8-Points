import AllS.Units.N_GI.N_disphenoid.N_sine_rule

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tetra_acute_equal_radii_opposite (A : Fin 4 → Point) (R : ℝ)
    (hf : ∀i : Fin 4,∃t : Affine.Triangle ℝ Point,t.points=A ∘ i.succAbove ∧
      t.circumradius=R ∧ t.AcuteAngled) :
    dist (A 0) (A 1)=dist (A 2) (A 3) ∧
    dist (A 0) (A 2)=dist (A 1) (A 3) ∧
    dist (A 0) (A 3)=dist (A 1) (A 2) := by
  obtain ⟨t0,ht0,hr0,ha0⟩ := hf 0
  obtain ⟨t1,ht1,hr1,ha1⟩ := hf 1
  obtain ⟨t2,ht2,hr2,ha2⟩ := hf 2
  obtain ⟨t3,ht3,hr3,ha3⟩ := hf 3
  have h0 := acute_triangle_principal_sum t0 ha0
  have h1 := acute_triangle_principal_sum t1 ha1
  have h2 := acute_triangle_principal_sum t2 ha2
  have h3 := acute_triangle_principal_sum t3 ha3
  rw [ht0,hr0] at h0
  rw [ht1,hr1] at h1
  rw [ht2,hr2] at h2
  rw [ht3,hr3] at h3
  change edgePrincipalAngle R (A 1) (A 2)+edgePrincipalAngle R (A 1) (A 3)+edgePrincipalAngle R (A 2) (A 3)=Real.pi at h0
  change edgePrincipalAngle R (A 0) (A 2)+edgePrincipalAngle R (A 0) (A 3)+edgePrincipalAngle R (A 2) (A 3)=Real.pi at h1
  change edgePrincipalAngle R (A 0) (A 1)+edgePrincipalAngle R (A 0) (A 3)+edgePrincipalAngle R (A 1) (A 3)=Real.pi at h2
  change edgePrincipalAngle R (A 0) (A 1)+edgePrincipalAngle R (A 0) (A 2)+edgePrincipalAngle R (A 1) (A 2)=Real.pi at h3
  have h01 : edgePrincipalAngle R (A 0) (A 1)=edgePrincipalAngle R (A 2) (A 3) := by linarith
  have h02 : edgePrincipalAngle R (A 0) (A 2)=edgePrincipalAngle R (A 1) (A 3) := by linarith
  have h03 : edgePrincipalAngle R (A 0) (A 3)=edgePrincipalAngle R (A 1) (A 2) := by linarith
  have d01 := acute_triangle_edge_length t3 ha3 0 2 1 (by decide) (by decide) (by decide)
  have d23 := acute_triangle_edge_length t0 ha0 1 0 2 (by decide) (by decide) (by decide)
  have d02 := acute_triangle_edge_length t3 ha3 0 1 2 (by decide) (by decide) (by decide)
  have d13 := acute_triangle_edge_length t0 ha0 0 1 2 (by decide) (by decide) (by decide)
  have d03 := acute_triangle_edge_length t2 ha2 0 1 2 (by decide) (by decide) (by decide)
  have d12 := acute_triangle_edge_length t0 ha0 0 2 1 (by decide) (by decide) (by decide)
  rw [ht3,hr3] at d01 d02
  rw [ht0,hr0] at d23 d13 d12
  rw [ht2,hr2] at d03
  change dist (A 0) (A 1)=2*R*Real.sin (edgePrincipalAngle R (A 0) (A 1)) at d01
  change dist (A 2) (A 3)=2*R*Real.sin (edgePrincipalAngle R (A 2) (A 3)) at d23
  change dist (A 0) (A 2)=2*R*Real.sin (edgePrincipalAngle R (A 0) (A 2)) at d02
  change dist (A 1) (A 3)=2*R*Real.sin (edgePrincipalAngle R (A 1) (A 3)) at d13
  change dist (A 0) (A 3)=2*R*Real.sin (edgePrincipalAngle R (A 0) (A 3)) at d03
  change dist (A 1) (A 2)=2*R*Real.sin (edgePrincipalAngle R (A 1) (A 2)) at d12
  exact ⟨by rw [d01,d23,h01],by rw [d02,d13,h02],by rw [d03,d12,h03]⟩

theorem disphenoid_opposite_lengths (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    dist (A 0) (A 1)=dist (A 2) (A 3) ∧
    dist (A 0) (A 2)=dist (A 1) (A 3) ∧
    dist (A 0) (A 3)=dist (A 1) (A 2) := by
  apply tetra_acute_equal_radii_opposite A (Real.sqrt (1-c^2))
  intro i
  obtain ⟨t,ht,_,hr,ha⟩ := disphenoid_acute_equal_circumradius A B c hc hAunit hBunit hAinj hBinj hcross hmatched i
  exact ⟨t,ht,hr,ha⟩

#print axioms tetra_acute_equal_radii_opposite
#print axioms disphenoid_opposite_lengths
end Blueprint.Thomson.Tail.Implementation
