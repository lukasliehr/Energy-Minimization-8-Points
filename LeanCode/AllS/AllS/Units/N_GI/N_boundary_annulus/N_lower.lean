import AllS.Units.N_GI.N_boundary_annulus.N_product_equation

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem eight_product_le_mean (u : Fin 8 → ℝ) (hu : ∀i,0≤u i) :
    (Finset.univ.prod (fun i : Fin 8 => 1+u i))≤(1+(∑i,u i)/8)^8 := by
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin 8 => (1:ℝ))
    (fun i=>1+u i) (by intros; norm_num) (by norm_num) (fun i _=>by linarith [hu i])
  have hn : 0≤Finset.univ.prod (fun i : Fin 8 => 1+u i) := Finset.prod_nonneg (fun i _=>by linarith [hu i])
  have he : ((Finset.univ.prod (fun i : Fin 8 => 1+u i))^(1/8:ℝ))^8=Finset.univ.prod (fun i : Fin 8 => 1+u i) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hn]
    norm_num
  norm_num [Finset.sum_add_distrib] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hn _) h 8
  rw [he] at hp
  calc
    _ ≤ ((8+(∑i,u i))/8)^8 := hp
    _ = _ := by congr 1; ring

theorem boundary_annulus_lower_scalar (u : Fin 8 → ℝ) (hu : ∀i,0≤u i)
    (he : (Finset.univ.prod (fun i : Fin 8 => 1+u i))=(250/239:ℝ)^2) : 181/2000<∑i,u i := by
  have h := eight_product_le_mean u hu
  rw [he] at h
  by_contra hn
  have hsum : ∑i,u i≤181/2000 := le_of_not_gt hn
  have hpos : 0≤1+(∑i,u i)/8 := by
    have hs : 0≤∑i,u i := Finset.sum_nonneg (fun i _=>hu i)
    linarith
  have hp := pow_le_pow_left₀ hpos (show 1+(∑i,u i)/8≤1+181/16000 by linarith) 8
  have hr : (1+181/16000:ℝ)^8<(250/239:ℝ)^2 := by norm_num
  linarith

theorem boundary_annulus_lower (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) : 181/2000<gnomonicSquareSum Y :=
  boundary_annulus_lower_scalar (fun i=>‖gnomonicTangent Y i‖^2) (fun _=>sq_nonneg _)
    (boundary_annulus_product_equation Y hY hal hg).1

#print axioms boundary_annulus_lower
end Blueprint.Thomson.Tail.Implementation
