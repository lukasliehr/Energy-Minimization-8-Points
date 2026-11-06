import AllS.Units.N_GI.N_variance_basic.N_centering_projection
import AllS.Units.N_GI.N_constants.N_pair_table
import AllS.Units.N_GI.N_contact_taylor.N_cubic_remainder

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def varianceSigmaH : ℝ := (11/50)*√(contactTotalWeight/4)
def varianceSigma : ℝ := 2+varianceSigmaH
def contactLinearArray (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactLinear q e.1 (contactNext e)
def contactQuadraticArray (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactQuadratic q e.1 (contactNext e)
def contactRemainderArray (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactRemainder q e.1 (contactNext e)
def contactDeltaArray (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactDelta q e.1 (contactNext e)

theorem contact_incident_sum (u : Fin 8→ℝ) :
    (∑ e : ContactIndex, contactWeight e*(u e.1+u (contactNext e)))=
      (contactTotalWeight/4)*(∑ i, u i) := by
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,contactWeight,contactNext,
    contactTotalWeight,contactKappa_formula,Fin.add_def,Fin.succ]
  ring

theorem contactArray_expansion (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    contactDeltaArray q=fun e=>contactLinearArray q e+contactQuadraticArray q e+contactRemainderArray q e := by
  funext e
  apply contact_taylor_exact_expansion q hq
  rw [packingReference_inner_cyclic,if_neg (contactNext_ne e),if_pos (contactNext_contact e)]

theorem contactRemainderArray_bound (q : TangentCoordinates) (hq : ‖q‖≤3/10) (e : ContactIndex) :
    |contactRemainderArray q e|≤(11/50)*(‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2) := by
  have hc : inner ℝ (packingReference e.1) (packingReference (contactNext e))=packingHeight := by
    rw [packingReference_inner_cyclic,if_neg (contactNext_ne e),if_pos (contactNext_contact e)]
  obtain ⟨h,hcU⟩ := contact_taylor_cubic_remainder q hq e.1 (contactNext e) hc
  exact h.trans (mul_le_mul_of_nonneg_right hcU.le (by positivity))

theorem contactRemainderArray_norm (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    contactNorm (contactRemainderArray q)≤varianceSigmaH*‖q‖^2 := by
  have hpoint (e : ContactIndex) : (contactRemainderArray q e)^2≤
      (11/50:ℝ)^2*‖q‖^2*(‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2) := by
    have h := contactRemainderArray_bound q hq e
    have hb := tangentVector_pair_norm_sq q e.1 (contactNext e) (contactNext_ne e)
    have hbP : 0≤‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2 := by positivity
    have h1 := mul_nonneg (sub_nonneg.mpr h) (by positivity : 0≤
      (11/50:ℝ)*(‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2)+|contactRemainderArray q e|)
    have h2 := mul_nonneg (sub_nonneg.mpr hb) hbP
    nlinarith [sq_abs (contactRemainderArray q e)]
  have hs : (contactNorm (contactRemainderArray q))^2≤
      (11/50:ℝ)^2*‖q‖^2*((contactTotalWeight/4)*‖q‖^2) := by
    rw [contactNorm_sq]
    calc
      _ ≤ ∑ e : ContactIndex, contactWeight e*((11/50:ℝ)^2*‖q‖^2*
          (‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2)) :=
        Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_left (hpoint e) (contactWeight_pos e).le)
      _ = (11/50:ℝ)^2*‖q‖^2*(∑ e : ContactIndex, contactWeight e*
          (‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _; ring
      _ = _ := by rw [contact_incident_sum (fun i=>‖tangentVector q i‖^2),tangentVector_sum_norm_sq]
  have hroot : (√(contactTotalWeight/4))^2=contactTotalWeight/4 :=
    Real.sq_sqrt (div_nonneg contactTotalWeight_pos.le (by norm_num))
  have hvP : 0≤varianceSigmaH := by dsimp [varianceSigmaH]; positivity
  have hv : varianceSigmaH^2=(11/50:ℝ)^2*(contactTotalWeight/4) := by
    dsimp [varianceSigmaH]
    rw [mul_pow,hroot]
  have hsq : (contactNorm (contactRemainderArray q))^2≤(varianceSigmaH*‖q‖^2)^2 := by
    rw [mul_pow,hv]
    nlinarith [hs]
  nlinarith [contactNorm_nonneg (contactRemainderArray q),mul_nonneg hvP (sq_nonneg ‖q‖)]

theorem variance_basic_remainder_norm (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    contactNorm (contactCenter (contactRemainderArray q))≤varianceSigmaH*‖q‖^2 :=
  (contactNorm_center_le _).trans (contactRemainderArray_norm q hq)

#print axioms variance_basic_remainder_norm
end Blueprint.Thomson.Tail.Implementation
