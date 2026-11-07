import AllS.Units.N_GI.N_boundary_annulus.N_product_equation

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem capped_sum_squares {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ) (κ : ℝ)
    (hu : ∀i∈s,0≤u i) (hk : 1/2≤κ) (hcap : ∀i∈s,u i≤κ*(∑j∈s,u j)) :
    (∑i∈s,(u i)^2)≤(κ^2+(1-κ)^2)*(∑i∈s,u i)^2 := by
  let S : ℝ := ∑i∈s,u i
  have hS : 0≤S := Finset.sum_nonneg hu
  by_cases hsmall : ∀i∈s,u i≤S/2
  · have hb : (∑i∈s,(u i)^2)≤(S/2)*S := by
      calc
        _ ≤ ∑i∈s,(S/2)*u i := Finset.sum_le_sum (fun i hi=>by nlinarith [hu i hi,hsmall i hi])
        _ = _ := by rw [←Finset.mul_sum]
    have hc : 1/2≤κ^2+(1-κ)^2 := by nlinarith [sq_nonneg (κ-1/2)]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg S)
    dsimp [S] at *
    nlinarith [hb,hm]
  · push_neg at hsmall
    obtain ⟨i,hi,hM⟩ := hsmall
    have herase : ∑j∈s.erase i,u j=S-u i := by
      have he := Finset.sum_erase_add s u hi
      dsimp [S]
      linarith
    have hqerase : ∑j∈s.erase i,(u j)^2=(∑j∈s,(u j)^2)-(u i)^2 := by
      have he := Finset.sum_erase_add s (fun j=>(u j)^2) hi
      linarith
    have hrest := Finset.sum_sq_le_sq_sum_of_nonneg (s:=s.erase i) (f:=u)
      (fun j hj=>hu j (Finset.mem_of_mem_erase hj))
    rw [herase,hqerase] at hrest
    have hb : u i≤κ*S := hcap i hi
    have hprod := mul_nonneg (sub_nonneg.mpr hb)
      (show 0≤κ*S+u i-S by nlinarith [mul_nonneg (by linarith : 0≤κ-1/2) hS])
    change (∑j∈s,(u j)^2)≤(κ^2+(1-κ)^2)*S^2
    nlinarith [hrest,hprod]

theorem boundary_annulus_sum_squares (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) :
    (∑i,‖gnomonicTangent Y i‖^4)≤
      ((1-√2/8)^2+(√2/8)^2)*(gnomonicSquareSum Y)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hk : (1/2:ℝ)≤1-√2/8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have h := capped_sum_squares Finset.univ (fun i=>‖gnomonicTangent Y i‖^2) (1-√2/8)
    (fun _ _=>sq_nonneg _) hk (fun i _=>(boundary_annulus_product_equation Y hY hal hg).2 i)
  simpa only [←pow_mul,show 2*2=4 from rfl,sub_sub_cancel,gnomonicSquareSum] using h

#print axioms boundary_annulus_sum_squares
end Blueprint.Thomson.Tail.Implementation
