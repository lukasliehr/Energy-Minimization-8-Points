import AllS.Units.N_GI.N_incident_bound.N_jensen_incident

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contactIncident_card : ∀ i : Fin 8, (contactIncident i).card=4 := by decide

theorem contactBi_pos_and_lt (p : ℝ) (q : TangentCoordinates) (i : Fin 8) :
    0<contactBi p q i ∧ contactBi p q i<contactJ p q := by
  have hI : (contactIncident i).Nonempty := Finset.card_pos.mp (by rw [contactIncident_card]; norm_num)
  have hC : (contactIncident i)ᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl,contactIncident_card]
    decide)
  have hc := Finset.sum_pos (fun e (_ : e∈(contactIncident i)ᶜ)=>Real.exp_pos (-contactScaledLinear p q e)) hC
  rw [contactBi_complement] at hc
  exact ⟨Finset.sum_pos (fun e _=>Real.exp_pos _) hI,by linarith⟩

theorem incident_quartic_decreasing (C b B : ℝ) (hb : 0≤b) (hCb : C≤4*b)
    (hbB : b≤B) (hBC : B≤C) : B*(C-B)^3≤b*(C-b)^3 := by
  have ht : 0≤B-b := sub_nonneg.mpr hbB
  have hu : 0≤C-B := sub_nonneg.mpr hBC
  have hd : 0≤3*b-(C-B) := by linarith
  have he : b*(C-b)^3-B*(C-B)^3=
      (B-b)*((C-B)^2*(3*b-(C-B))+3*b*(C-B)*(B-b)+b*(B-b)^2) := by ring
  apply sub_nonneg.mp
  rw [he]
  positivity

theorem incident_bound_bi_upper (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (i : Fin 8) : contactBi p q i<(51:ℝ)/10 := by
  by_contra hn
  have hb : (51:ℝ)/10≤contactBi p q i := le_of_not_gt hn
  obtain ⟨hBP,hBJ⟩ := contactBi_pos_and_lt p q i
  have hJC : contactJ p q<(3917:ℝ)/250 := hq.2.2.trans_lt (tail_Cstar_upper p hp).2
  have hBC := hBJ.trans hJC
  have hpow := pow_le_pow_left₀ (show 0≤contactJ p q-contactBi p q i by linarith)
    (show contactJ p q-contactBi p q i≤(3917:ℝ)/250-contactBi p q i by linarith) 3
  have hupper := mul_le_mul_of_nonneg_left hpow hBP.le
  have hdec := incident_quartic_decreasing ((3917:ℝ)/250) ((51:ℝ)/10) (contactBi p q i)
    (by norm_num) (by norm_num) hb hBC.le
  have hCmin := tail_Cmin_constants.1
  have hlower := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤15457/1000) hCmin.le 4) (by norm_num : (0:ℝ)≤27/256)
  have h := hlower.trans ((incident_bound_jensen_incident p q i).trans (hupper.trans hdec))
  norm_num at h

#print axioms incident_bound_bi_upper
end Blueprint.Thomson.Tail.Implementation
