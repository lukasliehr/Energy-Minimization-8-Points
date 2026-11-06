import AllS.Units.N_FI.N_exclude_six.N_realization

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem exclude_six_counted {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (h01 : bpairCounts a Y r t 0 1=1) (h02 : bpairCounts a Y r t 0 2=1)
    (h12 : bpairCounts a Y r t 1 2=1) : False := by
  obtain ⟨R⟩ := six_type_realization h h3 r t hrt hB h01 h02 h12
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [h.physical.1]
  have ha1 : a < 1 := by linarith [h.physical.2]
  let e := bpairE a (Y r) (Y t)
  let g := bpairG a (Y r) (Y t)
  let xi : Fin 6 → ℝ := fun k => inner ℝ g (Y (R.label k))
  have hBn : inner ℝ (Y r) (Y t)=2*a-1 := hB
  have hc (k : Fin 6) := exclude_six_type_coordinates a (Y r) (Y t) (Y (R.label k))
    ha0 ha1 (h.configuration.1 r) (h.configuration.1 t) (h.configuration.1 (R.label k))
    hBn (sixU a k) (sixV a k) (xi k) (R.left_type k) (R.right_type k) rfl
  have he (k : Fin 6) : inner ℝ e (Y (R.label k))=sixFirst a k := (hc k).1
  have hn : SixTypeNorms a xi := fun k => (hc k).2.2
  obtain ⟨hgr,hgt⟩ := bpair_G_endpoints a (Y r) (Y t) ha0 ha1
  change inner ℝ g (Y r)=0 at hgr
  change inner ℝ g (Y t)=0 at hgt
  have hz : (∑ k, xi k)=0 := by
    have hs := (zero_tensors_arbitrary_moments Y h1 h3 g).1
    rw [R.sum hrt,hgr,hgt,zero_add,zero_add] at hs
    exact hs
  have hm : (∑ k, (sixFirst a k)^2*xi k)=0 := by
    have hs := oddMoment_three_mixed Y h3 e e g
    rw [R.sum hrt,hgr,hgt,mul_zero,mul_zero,zero_add,zero_add] at hs
    simp_rw [he] at hs
    simpa only [pow_two] using hs
  have hcube : (∑ k, (xi k)^3)=0 := by
    have hs := oddMoment_zero_contraction 3 Y h3 g
    rw [R.sum hrt,hgr,hgt,zero_pow (by decide : 3 ≠ 0),zero_add,zero_add] at hs
    exact hs
  have hsq01 : (xi 0)^2=(xi 1)^2 :=
    bpair_reversed_coordinate_squares a (Y r) (Y t) (Y (R.label 0)) (Y (R.label 1))
      ha0 ha1 (h.configuration.1 r) (h.configuration.1 t)
      (h.configuration.1 _) (h.configuration.1 _) hBn _ _
      (R.left_type 0) (R.right_type 0) (R.left_type 1) (R.right_type 1)
  have hsq23 : (xi 2)^2=(xi 3)^2 :=
    bpair_reversed_coordinate_squares a (Y r) (Y t) (Y (R.label 2)) (Y (R.label 3))
      ha0 ha1 (h.configuration.1 r) (h.configuration.1 t)
      (h.configuration.1 _) (h.configuration.1 _) hBn _ _
      (R.left_type 2) (R.right_type 2) (R.left_type 3) (R.right_type 3)
  have hsq45 : (xi 4)^2=(xi 5)^2 :=
    bpair_reversed_coordinate_squares a (Y r) (Y t) (Y (R.label 4)) (Y (R.label 5))
      ha0 ha1 (h.configuration.1 r) (h.configuration.1 t)
      (h.configuration.1 _) (h.configuration.1 _) hBn _ _
      (R.left_type 4) (R.right_type 4) (R.left_type 5) (R.right_type 5)
  obtain ⟨hl3,hl12⟩ := exclude_six_linear_tensor_reduction a h.physical xi hz hm
  have hxi := (exclude_six_cubic_tensor_reduction a h.physical xi hn hsq01 hsq23 hsq45 hl3 hl12 hcube).1
  exact exclude_six_forbidden_inner a h.physical (Y r) (Y t) (Y (R.label 0)) (Y (R.label 1))
    (h.configuration.1 _) (h.configuration.1 _) (h.configuration.1 _) (h.configuration.1 _) hBn
    (R.left_type 0) (R.right_type 0) (R.left_type 1) (R.right_type 1) hxi
    (h.allowed_contact _ _ (R.injective.ne (by decide)))

theorem exclude_six_exclude (a : ℝ) (Y : Fin 8 → Point) (ha : physical a)
    (hY : IsConfiguration Y) (hc : AllowedContacts a Y)
    (hodd : ∀ i, (∑ j, inner ℝ (Y i) (Y j))=0 ∧ (∑ j, (inner ℝ (Y i) (Y j))^3)=0)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (h01 : bpairCounts a Y r t 0 1=1) (h02 : bpairCounts a Y r t 0 2=1)
    (h12 : bpairCounts a Y r t 1 2=1) : False := by
  have h : ContactCountData a Y := ⟨ha,hY,(vertex_contact_counts a ha).2 Y hY hc hodd⟩
  obtain ⟨h1,h3⟩ := (zero_tensors_equivalence Y).mp hodd
  exact exclude_six_counted h h1 h3 r t hrt hB h01 h02 h12

#check exclude_six_exclude
#print axioms exclude_six_exclude
end Blueprint.Thomson.Finite
