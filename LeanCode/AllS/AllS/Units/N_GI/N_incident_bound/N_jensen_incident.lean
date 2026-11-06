import AllS.Units.N_GI.N_contact_weights.N_assemble
import AllS.Units.N_GI.N_variance_basic.N_centering_projection

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactIncident (i : Fin 8) : Finset ContactIndex :=
  Finset.univ.filter (fun e=>e.1=i ∨ contactNext e=i)
def contactBi (p : ℝ) (q : TangentCoordinates) (i : Fin 8) : ℝ :=
  ∑ e∈contactIncident i, exp (-contactScaledLinear p q e)

theorem contact_exp_balanced (p : ℝ) (q : TangentCoordinates) (e : ContactIndex) :
    exp (-contactScaledLinear p q e)=balancedLambda*contactWeight e*exp (-contactLinearBalancedX p q e) := by
  have h := balancedZ_exponential e
  have he : -contactLinearBalancedX p q e=balancedZ e+(-contactScaledLinear p q e) := by
    dsimp [contactLinearBalancedX]
    ring
  rw [he,Real.exp_add]
  calc
    _ = (balancedLambda*contactWeight e*exp (balancedZ e))*exp (-contactScaledLinear p q e) := by rw [h]; ring
    _ = _ := by ring

theorem contactSubset_jensen (p : ℝ) (q : TangentCoordinates) (s : Finset ContactIndex)
    (hW : 0<∑ e∈s, contactWeight e) :
    balancedLambda*(∑ e∈s, contactWeight e)*
      exp ((∑ e∈s, contactWeight e*(-contactLinearBalancedX p q e))/(∑ e∈s, contactWeight e)) ≤
        ∑ e∈s, exp (-contactScaledLinear p q e) := by
  have h := mul_le_mul_of_nonneg_left
    (finite_weighted_exp_jensen s contactWeight (fun e=>-contactLinearBalancedX p q e)
      (fun e _=>(contactWeight_pos e).le) hW) (show 0≤balancedLambda from (Real.exp_pos _).le)
  calc
    _ ≤ balancedLambda*(∑ e∈s, contactWeight e*exp (-contactLinearBalancedX p q e)) := by simpa [mul_assoc] using h
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simpa [mul_assoc] using (contact_exp_balanced p q e).symm

theorem contactIncident_weight (i : Fin 8) :
    (∑ e∈contactIncident i, contactWeight e)=contactTotalWeight/4 := by
  simpa [contactIncident,Finset.sum_filter] using contactWeight_incident i

theorem contactIncident_complement_weight (i : Fin 8) :
    (∑ e∈(contactIncident i)ᶜ, contactWeight e)=3*contactTotalWeight/4 := by
  have h := Finset.sum_compl_add_sum (contactIncident i) contactWeight
  rw [contactIncident_weight,contactWeight_sum] at h
  linarith

theorem contactBi_complement (p : ℝ) (q : TangentCoordinates) (i : Fin 8) :
    (∑ e∈(contactIncident i)ᶜ, exp (-contactScaledLinear p q e))=contactJ p q-contactBi p q i := by
  have h := Finset.sum_compl_add_sum (contactIncident i) (fun e=>exp (-contactScaledLinear p q e))
  change (∑ e∈(contactIncident i)ᶜ, exp (-contactScaledLinear p q e))+contactBi p q i=contactJ p q at h
  linarith

theorem incident_bound_jensen_incident (p : ℝ) (q : TangentCoordinates) (i : Fin 8) :
    (27:ℝ)/256*(balancedLambda*contactTotalWeight)^4≤contactBi p q i*(contactJ p q-contactBi p q i)^3 := by
  let m : ℝ := ∑ e∈contactIncident i, contactWeight e*contactLinearBalancedX p q e
  have hi := contactSubset_jensen p q (contactIncident i) (by rw [contactIncident_weight]; exact div_pos contactTotalWeight_pos (by norm_num))
  have hc := contactSubset_jensen p q (contactIncident i)ᶜ (by
    rw [contactIncident_complement_weight]
    exact div_pos (mul_pos (by norm_num) contactTotalWeight_pos) (by norm_num))
  have hmeanI : (∑ e∈contactIncident i, contactWeight e*(-contactLinearBalancedX p q e))=-m := by
    simp [m,mul_neg,Finset.sum_neg_distrib]
  have hmeanC : (∑ e∈(contactIncident i)ᶜ, contactWeight e*(-contactLinearBalancedX p q e))=m := by
    have h := Finset.sum_compl_add_sum (contactIncident i) (fun e=>contactWeight e*contactLinearBalancedX p q e)
    rw [contactLinearBalancedX_mean] at h
    simp only [mul_neg,Finset.sum_neg_distrib]
    change _+m=0 at h
    linarith
  rw [contactIncident_weight,hmeanI] at hi
  change balancedLambda*(contactTotalWeight/4)*exp (-m/(contactTotalWeight/4))≤contactBi p q i at hi
  rw [contactIncident_complement_weight,hmeanC,contactBi_complement] at hc
  have hA : 0≤balancedLambda*(contactTotalWeight/4)*exp (-m/(contactTotalWeight/4)) := by
    have := contactTotalWeight_pos
    dsimp [balancedLambda]
    positivity
  have hB : 0≤balancedLambda*(3*contactTotalWeight/4)*exp (m/(3*contactTotalWeight/4)) := by
    have := contactTotalWeight_pos
    dsimp [balancedLambda]
    positivity
  have hm := mul_le_mul hi (pow_le_pow_left₀ hB hc 3) (pow_nonneg hB 3) (hA.trans hi)
  have hexp : exp (-m/(contactTotalWeight/4))*(exp (m/(3*contactTotalWeight/4)))^3=1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    norm_num only [Nat.cast_ofNat]
    have he : -m/(contactTotalWeight/4)+(3:ℝ)*(m/(3*contactTotalWeight/4))=0 := by ring
    rw [he,Real.exp_zero]
  have hident : (balancedLambda*(contactTotalWeight/4)*exp (-m/(contactTotalWeight/4)))*
      (balancedLambda*(3*contactTotalWeight/4)*exp (m/(3*contactTotalWeight/4)))^3=
        (27:ℝ)/256*(balancedLambda*contactTotalWeight)^4 := by
    calc
      _ = ((27:ℝ)/256*(balancedLambda*contactTotalWeight)^4)*
          (exp (-m/(contactTotalWeight/4))*(exp (m/(3*contactTotalWeight/4)))^3) := by ring
      _ = _ := by rw [hexp,mul_one]
  rwa [hident] at hm

#print axioms incident_bound_jensen_incident
end Blueprint.Thomson.Tail.Implementation
