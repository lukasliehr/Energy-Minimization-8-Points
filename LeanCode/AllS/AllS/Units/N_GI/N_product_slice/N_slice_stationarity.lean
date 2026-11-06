import AllS.Units.N_GI.N_product_slice.N_gnomonic_inverse
import AllS.Units.N_GI.N_product_gauge.N_chord_stationarity

noncomputable section
open Real SquareAntiprismVerification Filter
namespace Blueprint.Thomson.Tail.Implementation

theorem gnomonic_cross (Y : Fin 8 → Point) (i : Fin 8) :
    crossVec (packingReference i) (gnomonicTangent Y i)=
      (productFactor Y i)⁻¹ • crossVec (packingReference i) (Y i) := by
  ext k
  fin_cases k <;> simp [crossVec,gnomonicTangent] <;> ring

theorem product_slice_slice_stationarity (Y : Fin 8 → Point)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) :
    (∑i,crossVec (packingReference i) (gnomonicTangent Y i))=0 := by
  have hsi (i : Fin 8) : 0<productFactor Y i := (product_slice_positive_factors Y hal hp i).1
  ext k
  let g : Fin 8 → ℝ → ℝ := fun i t => inner ℝ (packingReference i) (axisRotate k t (Y i))
  have hg0 (i : Fin 8) : g i 0=productFactor Y i := by simp [g,productFactor]
  have hd (i : Fin 8) : HasDerivAt (g i) (-(crossVec (packingReference i) (Y i)) k) 0 :=
    axisRotate_inner_hasDerivAt k (packingReference i) (Y i)
  have he : ∀ᶠt in nhds (0:ℝ),∀i,0<g i t := by
    apply Filter.eventually_all.mpr
    intro i
    exact continuousAt_const.eventually_lt (hd i).continuousAt (by rw [hg0];exact hsi i)
  let f : ℝ → ℝ := fun t => ∑i,log (g i t)
  have hf : HasDerivAt f (∑i,-(crossVec (packingReference i) (Y i)) k/productFactor Y i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [hg0] using (hd i).log (by rw [hg0];exact (hsi i).ne')
  have hmax : IsLocalMax f 0 := by
    filter_upwards [he] with t ht
    have hm := hal (axisRotationOperator k t,Equiv.refl _) ⟨axisRotationOperator_mem k t,Set.mem_univ _⟩
    have hleft : gaugeProduct Y (axisRotationOperator k t,Equiv.refl _) =∏i,g i t := by
      apply Finset.prod_congr rfl
      intro i _
      exact max_eq_left (ht i).le
    have hright : (∏i,max (productFactor Y i) 0)=∏i,g i 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hg0,max_eq_left (hsi i).le]
    rw [hleft,hright] at hm
    change f t≤f 0
    change (∑i,log (g i t))≤∑i,log (g i 0)
    rw [←Real.log_prod (fun i _ => (ht i).ne'),←Real.log_prod (fun i _ => by rw [hg0];exact (hsi i).ne')]
    exact Real.log_le_log (Finset.prod_pos (fun i _ => ht i)) hm
  have hz := hmax.hasDerivAt_eq_zero hf
  have heq : (∑i,-(crossVec (packingReference i) (Y i)) k/productFactor Y i)=
      -(∑i,(crossVec (packingReference i) (gnomonicTangent Y i)) k) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [gnomonic_cross,PiLp.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [heq,neg_eq_zero] at hz
  simpa only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.zero_apply] using hz

#print axioms product_slice_slice_stationarity
end Blueprint.Thomson.Tail.Implementation
