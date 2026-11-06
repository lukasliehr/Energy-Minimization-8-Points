import AllS.Units.N_F.N_bpair_balance
import AllS.Units.N_FI.N_bpair_cases.N_eta_interval

noncomputable section
namespace Blueprint.Thomson.Finite

theorem bpair_constant_identity (a : ℝ) :
    2*(1+contacts a 1)^3+16*((contacts a 0)^3+(contacts a 2)^3+(contacts a 3)^3)= -4*bpairW a := by
  have hb := (contact_counts_baseline a).2.2
  norm_num [baselineCounts,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three] at hb
  dsimp [bpairW,contacts] at *
  linear_combination 8*hb

theorem bpair_symmetric_cubic_sum (a : ℝ) (n : Fin 3 → Fin 3 → ℝ)
    (hsym : ∀ u v, n u v=n v u) (hrow : ∀ u, (∑ v, n u v)=2) :
    (∑ u, ∑ v, n u v*(bContacts a u+bContacts a v)^3)=
      16*((contacts a 0)^3+(contacts a 2)^3+(contacts a 3)^3)+
        2*(n 0 1*bpairU a+n 0 2*bpairV a+n 1 2*bpairW a) := by
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  rw [Fin.sum_univ_three] at h0 h1 h2
  rw [hsym 1 0] at h1
  rw [hsym 2 0,hsym 2 1] at h2
  have hd0 : n 0 0=2-n 0 1-n 0 2 := by linarith
  have hd1 : n 1 1=2-n 0 1-n 1 2 := by linarith
  have hd2 : n 2 2=2-n 0 2-n 1 2 := by linarith
  have c0 : bContacts a 0=contacts a 0 := rfl
  have c1 : bContacts a 1=contacts a 2 := rfl
  have c2 : bContacts a 2=contacts a 3 := rfl
  simp only [Fin.sum_univ_three,c0,c1,c2]
  rw [hsym 1 0,hsym 2 0,hsym 2 1,hd0,hd1,hd2,(bpair_UVW_identities a).2.1]
  dsimp [bpairU,bpairV]
  ring

theorem bpair_cases_cubic_equation {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    bpairU a < 0 ∧ 0 < bpairW a ∧ bpairU a+bpairV a=bpairW a ∧
    (bpairCounts a Y r t 0 1:ℝ)*bpairU a+(bpairCounts a Y r t 0 2:ℝ)*bpairV a+
      (bpairCounts a Y r t 1 2:ℝ)*bpairW a=2*bpairW a := by
  let n : Fin 3 → Fin 3 → ℝ := fun u v => (bpairCounts a Y r t u v:ℝ)
  have hs := bpair_balance_symmetry h h3 r t hrt hB
  have hn : ∀ u v, n u v=n v u := by intro u v; dsimp [n]; exact_mod_cast hs u v
  have hr : ∀ u, (∑ v, n u v)=2 := by
    intro u
    dsimp [n]
    exact_mod_cast bpairCounts_row h r t hrt hB u
  have hc := bpair_symmetric_cubic_sum a n hn hr
  have hm := bpair_full_sum h r t hrt hB (fun x y => (x+y)^3)
  have hz : (∑ l, (inner ℝ (Y r) (Y l)+inner ℝ (Y t) (Y l))^3)=0 := by
    simpa only [inner_add_left] using oddMoment_zero_contraction 3 Y h3 (Y r+Y t)
  change _ = _+_+(∑ u, ∑ v, n u v*(bContacts a u+bContacts a v)^3) at hm
  rw [hz,hc] at hm
  have hconst := bpair_constant_identity a
  have hswap : (contacts a 1+1)^3=(1+contacts a 1)^3 := by ring
  rw [hswap] at hm
  refine ⟨(bpair_UW_signs a h.physical).1,(bpair_UW_signs a h.physical).2,
    (bpair_UVW_identities a).1,?_⟩
  change n 0 1*bpairU a+n 0 2*bpairV a+n 1 2*bpairW a=2*bpairW a
  linarith

#check bpair_cases_cubic_equation
#print axioms bpair_cases_cubic_equation
end Blueprint.Thomson.Finite
