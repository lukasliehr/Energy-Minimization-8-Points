import AllS.Units.N_GI.N_convex_domain.N_convexity
import AllS.Units.N_GI.N_balanced_energy.N_reference_data
import AllS.Units.N_GI.N_contact_spectrum.N_stress_zero
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem finite_weighted_exp_jensen {α : Type*} (s : Finset α) (w y : α→ℝ)
    (hw : ∀ i∈s, 0≤w i) (hW : 0<∑ i∈s, w i) :
    (∑ i∈s, w i)*exp ((∑ i∈s, w i*y i)/(∑ i∈s, w i))≤∑ i∈s, w i*exp (y i) := by
  have h := convexOn_exp.map_centerMass_le (p := y) hw hW (fun i _=>Set.mem_univ _)
  have h' : exp ((∑ i∈s, w i*y i)/(∑ i∈s, w i))≤(∑ i∈s, w i*exp (y i))/(∑ i∈s, w i) := by
    simpa [Finset.centerMass,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  simpa [mul_comm] using (le_div_iff₀ hW).mp h'

def contactLinearBalancedX (p : ℝ) (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactScaledLinear p q e-balancedZ e

theorem contactLinearBalancedX_mean (p : ℝ) (q : TangentCoordinates) :
    (∑ e : ContactIndex, contactWeight e*contactLinearBalancedX p q e)=0 := by
  have hl : (∑ e : ContactIndex, contactWeight e*contactScaledLinear p q e)=
      (p/tau)*(∑ e : ContactIndex, contactWeight e*contactLinear q e.1 (contactNext e)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [contactScaledLinear]
    ring
  simp only [contactLinearBalancedX,mul_sub,Finset.sum_sub_distrib,hl,
    contact_spectrum_stress_zero,balancedZ_mean,mul_zero,sub_zero]

theorem contactJ_balanced (p : ℝ) (q : TangentCoordinates) :
    contactJ p q=balancedLambda*(∑ e : ContactIndex, contactWeight e*exp (-contactLinearBalancedX p q e)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have h := balancedZ_exponential e
  have he : -contactLinearBalancedX p q e=balancedZ e+(-contactScaledLinear p q e) := by
    dsimp [contactLinearBalancedX]
    ring
  rw [he,Real.exp_add]
  calc
    _ = (balancedLambda*contactWeight e*exp (balancedZ e))*exp (-contactScaledLinear p q e) := by rw [h]; ring
    _ = _ := by ring

theorem weighted_exp_isolate (x : ContactIndex→ℝ)
    (hx : (∑ e, contactWeight e*x e)=0) (e : ContactIndex)
    (hw : contactWeight e<contactTotalWeight) :
    contactWeight e*exp (-x e)+(contactTotalWeight-contactWeight e)*
      exp (contactWeight e*x e/(contactTotalWeight-contactWeight e)) ≤
        ∑ f : ContactIndex, contactWeight f*exp (-x f) := by
  have hwSum : (∑ f∈Finset.univ.erase e, contactWeight f)=contactTotalWeight-contactWeight e := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset ContactIndex)) contactWeight (Finset.mem_univ e)
    rw [contactWeight_sum] at h
    linarith
  have hxSum : (∑ f∈Finset.univ.erase e, contactWeight f*(-x f))=contactWeight e*x e := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset ContactIndex))
      (fun f=>contactWeight f*x f) (Finset.mem_univ e)
    rw [hx] at h
    simp only [mul_neg,Finset.sum_neg_distrib]
    linarith
  have hj := finite_weighted_exp_jensen (Finset.univ.erase e) contactWeight (fun f=>-x f)
    (fun f _=>(le_trans (by norm_num) (contactWeight_ge_one f))) (by rw [hwSum]; linarith)
  rw [hwSum,hxSum] at hj
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset ContactIndex))
    (fun f=>contactWeight f*exp (-x f)) (Finset.mem_univ e)
  linarith

#print axioms weighted_exp_isolate
#print axioms contactJ_balanced
end Blueprint.Thomson.Tail.Implementation
