import AllS.Units.N_FI.N_bpair_balance.N_contingency

noncomputable section
namespace Blueprint.Thomson.Finite

theorem two_indices_sum (g : Fin 8 → ℝ) (r t : Fin 8) (hrt : r ≠ t) :
    (∑ l, g l)=g r+g t+(∑ l, if l ≠ r ∧ l ≠ t then g l else 0) := by
  have he (l : Fin 8) : g l=(if l=r then g r else 0)+(if l=t then g t else 0)+
      (if l ≠ r ∧ l ≠ t then g l else 0) := by
    by_cases hlr : l=r
    · subst l
      simp [hrt]
    · by_cases hlt : l=t
      · subst l
        simp [Ne.symm hrt]
      · simp [hlr,hlt]
  calc
    _ = ∑ l, ((if l=r then g r else 0)+(if l=t then g t else 0)+
        (if l ≠ r ∧ l ≠ t then g l else 0)) := Finset.sum_congr rfl (fun l _ => he l)
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib]; simp

theorem bpair_full_sum {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (f : ℝ → ℝ → ℝ) :
    (∑ l, f (inner ℝ (Y r) (Y l)) (inner ℝ (Y t) (Y l)))=
      f 1 (contacts a 1)+f (contacts a 1) 1+
        ∑ u, ∑ v, (bpairCounts a Y r t u v:ℝ)*f (bContacts a u) (bContacts a v) := by
  rw [two_indices_sum _ r t hrt,← bpair_cell_weight_sum h r t hrt hB f]
  have hr : inner ℝ (Y r) (Y r)=1 := by rw [real_inner_self_eq_norm_sq,h.configuration.1]; norm_num
  have ht : inner ℝ (Y t) (Y t)=1 := by rw [real_inner_self_eq_norm_sq,h.configuration.1]; norm_num
  rw [hr,ht,hB,real_inner_comm (Y r) (Y t),hB]

theorem bpair_balance_symmetry {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    ∀ u v, bpairCounts a Y r t u v=bpairCounts a Y r t v u := by
  let n : Fin 3 → Fin 3 → ℝ := fun u v => (bpairCounts a Y r t u v:ℝ)
  obtain ⟨_,hrow,hcol⟩ := bpair_balance_contingency h r t hrt hB
  have row (u : Fin 3) : (∑ v, n u v)=2 := by dsimp [n]; exact_mod_cast hrow u
  have col (v : Fin 3) : (∑ u, n u v)=2 := by dsimp [n]; exact_mod_cast hcol v
  have hc0 : (∑ l, (inner ℝ (Y r) (Y l)-inner ℝ (Y t) (Y l))^3)=0 := by
    simpa only [inner_sub_left] using oddMoment_zero_contraction 3 Y h3 (Y r-Y t)
  have hs := bpair_full_sum h r t hrt hB (fun x y => (x-y)^3)
  have hcancel : (1-contacts a 1)^3+(contacts a 1-1)^3=0 := by ring
  have hc : (∑ u, ∑ v, n u v*(bContacts a u-bContacts a v)^3)=0 := by
    change _ = (1-contacts a 1)^3+(contacts a 1-1)^3+_ at hs
    rw [hc0,hcancel,zero_add] at hs
    exact hs.symm
  let d := n 0 1-n 1 0
  have h20 : n 2 0=n 0 2+d := by
    have hr := row 0
    have hc := col 0
    rw [Fin.sum_univ_three] at hr hc
    dsimp [d]
    linarith
  have h12 : n 1 2=n 2 1+d := by
    have hr := row 1
    have hc := col 1
    rw [Fin.sum_univ_three] at hr hc
    dsimp [d]
    linarith
  have h01 : n 0 1=n 1 0+d := by dsimp [d]; ring
  have c0 : bContacts a 0=contacts a 0 := rfl
  have c1 : bContacts a 1=contacts a 2 := rfl
  have c2 : bContacts a 2=contacts a 3 := rfl
  simp only [Fin.sum_univ_three,c0,c1,c2] at hc
  rw [h20,h12,h01] at hc
  have hdprod : d*(3*(contacts a 0-contacts a 2)*(contacts a 2-contacts a 3)*(contacts a 3-contacts a 0))=0 := by
    linear_combination hc
  obtain ⟨_,hDB,hB0,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a h.physical
  have hne : 3*(contacts a 0-contacts a 2)*(contacts a 2-contacts a 3)*(contacts a 3-contacts a 0) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (by linarith)
      · linarith
    · linarith
  have hd : d=0 := (mul_eq_zero.mp hdprod).resolve_right hne
  rw [hd,add_zero] at h20 h12 h01
  intro u v
  have hn : n u v=n v u := by
    fin_cases u <;> fin_cases v
    all_goals first | rfl | exact h01 | exact h01.symm | exact h20 | exact h20.symm | exact h12 | exact h12.symm
  dsimp [n] at hn
  exact_mod_cast hn

#check bpair_balance_symmetry
#print axioms bpair_balance_symmetry
end Blueprint.Thomson.Finite
