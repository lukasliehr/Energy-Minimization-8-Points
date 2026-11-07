import AllS.Units.N_G.N_cycle_winding

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem force_convex_tan : ConvexOn ℝ (Set.Ioo (0:ℝ) (π/2)) tan := by
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) (π/2)) : HasDerivAt tan (1/cos x^2) x :=
    Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hx.1],hx.2⟩).ne'
  apply MonotoneOn.convexOn_of_deriv (convex_Ioo (0:ℝ) (π/2))
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (by simpa only [interior_Ioo] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    simp only [interior_Ioo] at hx hy
    rw [(hd x hx).deriv,(hd y hy).deriv]
    have hcos := Real.antitoneOn_cos ⟨hx.1.le,by linarith [hx.2,Real.pi_pos]⟩
      ⟨hy.1.le,by linarith [hy.2,Real.pi_pos]⟩ hxy
    have hcy := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hy.1],hy.2⟩
    have hcx := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hx.1],hx.2⟩
    apply (div_le_div_iff₀ (sq_pos_of_pos hcx) (sq_pos_of_pos hcy)).mpr
    nlinarith

theorem force_convex_cot : ConvexOn ℝ (Set.Ioo (0:ℝ) (π/2)) (fun x => (tan x)⁻¹) := by
  refine ⟨convex_Ioo _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : π/2-x ∈ Set.Ioo (0:ℝ) (π/2) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hy' : π/2-y ∈ Set.Ioo (0:ℝ) (π/2) := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have h := force_convex_tan.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a*(π/2-x)+b*(π/2-y)=π/2-(a*x+b*y) := by linear_combination (π/2)*hab
  rw [he,Real.tan_pi_div_two_sub,Real.tan_pi_div_two_sub,Real.tan_pi_div_two_sub] at h
  exact h

theorem force_jensen {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ S, α i ∈ Set.Ioo (0:ℝ) (π/2)) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ioo (0:ℝ) (π/2)) f) :
    (S.card:ℝ)*f ((∑ i ∈ S,α i)/S.card) ≤ ∑ i ∈ S,f (α i) := by
  have hn : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hw : ∑ _i ∈ S,(1:ℝ)/S.card=1 := by simp [hn.ne']
  have h := hf.map_sum_le (t:=S) (w:=fun _ => (1:ℝ)/S.card) (p:=α)
    (fun _ _ => by positivity) hw hα
  simp only [smul_eq_mul,← Finset.mul_sum] at h
  have hdiv : (1/(S.card:ℝ))*(∑ i ∈ S,α i)=(∑ i ∈ S,α i)/S.card := by ring
  rw [hdiv] at h
  have hh := mul_le_mul_of_nonneg_left h hn.le
  have hc : (S.card:ℝ)*((1/(S.card:ℝ))*(∑ i ∈ S,f (α i)))=∑ i ∈ S,f (α i) := by field_simp
  rwa [hc] at hh

#print axioms force_jensen
end Blueprint.Thomson.Tail.Implementation
