import AllS.Units.N_FI.N_exclude_six.N_cubic_tensor_reduction

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def sixForbiddenInner (a : ℝ) : ℝ := (a^2-6*a+1)/(4*a)

theorem sixForbiddenInner_bounds (a : ℝ) (ha : physical a) :
    contacts a 3 < sixForbiddenInner a ∧ sixForbiddenInner a < contacts a 1 := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsn := Real.sqrt_nonneg (2:ℝ)
  have hr0 : 1 < √(2:ℝ) := by nlinarith
  have hr1 : √(2:ℝ) < 2 := by nlinarith
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  have hc : 1/3 < (5+2*√(2:ℝ))/17 := by linarith
  have hfac : 0 < (5-2*√(2:ℝ))*((a-1)*(a-(5+2*√2)/17)) :=
    mul_pos (by linarith) (mul_pos_of_neg_of_neg (by linarith) (by linarith [ha.2]))
  have he : (a^2-6*a+1)-4*a*contacts a 3=
      (5-2*√(2:ℝ))*((a-1)*(a-(5+2*√2)/17)) := by
    change (a^2-6*a+1)-4*a*(-a-(1-a)/√2)=_
    simp only [div_eq_mul_inv,hinv]
    linear_combination (-4*(a-1)/17)*hs
  have hpoly := (contact_order_packing_bounds a ha.1 ha.2).2
  unfold sixForbiddenInner
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 4*a)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < 4*a)).mpr
    change a^2-6*a+1 < (2*a-1)*(4*a)
    nlinarith

theorem sixForbiddenInner_not_contact (a : ℝ) (ha : physical a) :
    sixForbiddenInner a ∉ Set.range (contacts a) := by
  obtain ⟨hD,hB⟩ := sixForbiddenInner_bounds a ha
  obtain ⟨_,hDB,hB0,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  rintro ⟨k,hk⟩
  fin_cases k
  · change contacts a 0=sixForbiddenInner a at hk
    linarith
  · change contacts a 1=sixForbiddenInner a at hk
    linarith
  · change contacts a 2=sixForbiddenInner a at hk
    linarith
  · change contacts a 3=sixForbiddenInner a at hk
    linarith

theorem exclude_six_forbidden_inner (a : ℝ) (ha : physical a) (x z y w : Point)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hw : ‖w‖=1)
    (hB : inner ℝ x z=2*a-1)
    (hxy : inner ℝ x y=contacts a 0) (hzy : inner ℝ z y=contacts a 2)
    (hxw : inner ℝ x w=contacts a 2) (hzw : inner ℝ z w=contacts a 0)
    (hgsum : inner ℝ (bpairG a x z) y+inner ℝ (bpairG a x z) w=0)
    (hcontact : inner ℝ y w ∈ Set.range (contacts a)) : False := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  obtain ⟨hey,hfy,hny⟩ := exclude_six_type_coordinates a x z y ha0 ha1 hx hz hy hB _ _ _ hxy hzy rfl
  obtain ⟨hew,hfw,_⟩ := exclude_six_type_coordinates a x z w ha0 ha1 hx hz hw hB _ _ _ hxw hzw rfl
  have hrevE : (contacts a 2+contacts a 0)/(2*√a)=bpairP a := by dsimp [bpairP]; ring
  have hrevF : (contacts a 2-contacts a 0)/(2*√(1-a))= -((contacts a 0-contacts a 2)/(2*√(1-a))) := by ring
  rw [hrevE] at hew
  rw [hrevF] at hfw
  change inner ℝ (bpairE a x z) y=bpairP a at hey
  change (bpairP a)^2+_+_=1 at hny
  have hp := bpair_frame_inner a x z y w ha0 ha1 hx hz hB
  rw [hey,hew,hfy,hfw] at hp
  have hgw : inner ℝ (bpairG a x z) w= -inner ℝ (bpairG a x z) y := by linarith
  rw [hgw] at hp
  have he : inner ℝ y w=2*(bpairP a)^2-1 := by nlinarith
  have hT : 2*(bpairP a)^2-1=sixForbiddenInner a := by
    rw [bpairP_square a ha0]
    unfold sixForbiddenInner
    field_simp
    ring
  rw [he,hT] at hcontact
  exact sixForbiddenInner_not_contact a ha hcontact

#check exclude_six_forbidden_inner
#print axioms exclude_six_forbidden_inner
end Blueprint.Thomson.Finite
