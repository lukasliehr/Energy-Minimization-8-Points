import ThomsonNegative.Geometry.ContactData
import ThomsonNegative.Geometry.Candidate
import ThomsonNegative.Geometry.SquareTools
import ThomsonNegative.Geometry.Tensors

/-! Generic contact-count, tensor, two-square and congruence geometry adapted
from read-only sources; no positive-s potential or CAP is imported. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/- Source: N_bpair_balance/N_contingency.lean -/

namespace ThomsonNegative.Geometry

/-- Exact geometric hypotheses for the contact classification, with actual counted neighbors. -/
structure ContactCountData (a : ℝ) (Y : Fin 8 → Point) : Prop where
  physical : physical a
  configuration : IsConfiguration Y
  counts : ∀ i, vertexContactCounts a Y i=baselineCounts

def bContactIndex : Fin 3 → Fin 4 := ![0,2,3]
def bContacts (a : ℝ) (u : Fin 3) : ℝ := contacts a (bContactIndex u)
def bpairCell (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) : Finset (Fin 8) :=
  Finset.univ.filter (fun l => l ≠ r ∧ l ≠ t ∧
    inner ℝ (Y r) (Y l)=bContacts a u ∧ inner ℝ (Y t) (Y l)=bContacts a v)
def bpairCounts (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) : ℕ :=
  (bpairCell a Y r t u v).card

theorem ContactCountData.allowed_contact {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (i j : Fin 8) (hij : i ≠ j) : inner ℝ (Y i) (Y j) ∈ Set.range (contacts a) := by
  classical
  let S := Finset.univ.biUnion (contactNeighbors a Y i)
  have hsub : S ⊆ Finset.univ.erase i := by
    intro l hl
    obtain ⟨k,_,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hl).2.1,Finset.mem_univ _⟩
  have hdis : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (contactNeighbors a Y i) := by
    intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro l hlu hlv
    have hu := (Finset.mem_filter.mp hlu).2.2
    have hv := (Finset.mem_filter.mp hlv).2.2
    exact huv (contact_injective a h.physical (hu.symm.trans hv))
  have hcard : S.card=7 := by
    rw [Finset.card_biUnion hdis]
    change (∑ k, vertexContactCounts a Y i k)=7
    rw [h.counts i]
    exact (contact_counts_baseline a).1
  have heq : S=Finset.univ.erase i := Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hj : j ∈ S := by rw [heq]; simp [Ne.symm hij]
  obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hj
  exact ⟨k,(Finset.mem_filter.mp hk).2.2.symm⟩

theorem ContactCountData.unique_B {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (i j k : Fin 8) (hij : i ≠ j) (hik : i ≠ k)
    (hj : inner ℝ (Y i) (Y j)=contacts a 1)
    (hk : inner ℝ (Y i) (Y k)=contacts a 1) : j=k := by
  have hcard : (contactNeighbors a Y i 1).card ≤ 1 := by
    have hc := congrFun (h.counts i) 1
    change (contactNeighbors a Y i 1).card=(1:ℕ) at hc
    omega
  apply (Finset.card_le_one.mp hcard) j _ k _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hij,hj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hik,hk⟩

theorem bContacts_injective (a : ℝ) (ha : physical a) : Function.Injective (bContacts a) :=
  (contact_injective a ha).comp (by decide : Function.Injective bContactIndex)

theorem bContactIndex_ne_one (u : Fin 3) : bContactIndex u ≠ 1 := by
  have h : ∀ u : Fin 3, bContactIndex u ≠ 1 := by decide
  exact h u

theorem bpair_remaining_types {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (l : Fin 8) (hlr : l ≠ r) (hlt : l ≠ t) :
    inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) ∧
    inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a) := by
  have one_side (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
      (hlr : l ≠ r) (hlt : l ≠ t) : inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) := by
    obtain ⟨k,hk⟩ := h.allowed_contact r l (Ne.symm hlr)
    have hk1 : k ≠ 1 := by
      intro he
      rw [he] at hk
      exact hlt (h.unique_B r l t (Ne.symm hlr) hrt hk.symm hB)
    have hcover : ∀ k : Fin 4, k ≠ 1 → ∃ u, bContactIndex u=k := by decide
    obtain ⟨u,hu⟩ := hcover k hk1
    exact ⟨u,by simpa only [bContacts,hu] using hk⟩
  exact ⟨one_side r t hrt hB hlr hlt,
    one_side t r (Ne.symm hrt) (by rw [real_inner_comm]; exact hB) hlt hlr⟩

theorem finite_fiber_count (S : Finset (Fin 8)) (g : Fin 8 → ℝ) (c : Fin 3 → ℝ)
    (hc : Function.Injective c) (hg : ∀ l ∈ S, g l ∈ Set.range c) :
    (∑ u, (S.filter (fun l => g l=c u)).card)=S.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ.image c) g
  rw [Finset.sum_image (by intro u _ v _ huv; exact hc huv)] at h
  have heq : S.filter (fun l => g l ∈ Finset.univ.image c)=S := by
    apply Finset.filter_eq_self.mpr
    intro l hl
    obtain ⟨u,hu⟩ := hg l hl
    exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,hu⟩
  rw [heq] at h
  exact h

theorem bpairCounts_row {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (u : Fin 3) : (∑ v, bpairCounts a Y r t u v)=2 := by
  let S := contactNeighbors a Y r (bContactIndex u)
  have hmem (l : Fin 8) (hl : l ∈ S) : l ≠ r ∧ l ≠ t := by
    obtain ⟨hlr,hprod⟩ := (Finset.mem_filter.mp hl).2
    refine ⟨hlr,?_⟩
    intro hlt
    rw [hlt,hB] at hprod
    exact bContactIndex_ne_one u ((contact_injective a h.physical hprod).symm)
  have hcell (v : Fin 3) : bpairCell a Y r t u v=
      S.filter (fun l => inner ℝ (Y t) (Y l)=bContacts a v) := by
    ext l
    constructor
    · intro hl
      obtain ⟨hlr,hlt,hu,hv⟩ := (Finset.mem_filter.mp hl).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlr,hu⟩,hv⟩
    · intro hl
      obtain ⟨hlS,hv⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hmem l hlS).1,(hmem l hlS).2,
        (Finset.mem_filter.mp hlS).2.2,hv⟩
  have hg : ∀ l ∈ S, inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a) := by
    intro l hl
    exact (bpair_remaining_types h r t hrt hB l (hmem l hl).1 (hmem l hl).2).2
  simp_rw [bpairCounts,hcell]
  rw [finite_fiber_count S _ _ (bContacts_injective a h.physical) hg]
  have hc := congrFun (h.counts r) (bContactIndex u)
  change S.card=baselineCounts (bContactIndex u) at hc
  rw [hc]
  fin_cases u <;> rfl

theorem bpairCounts_swap (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) (u v : Fin 3) :
    bpairCounts a Y r t u v=bpairCounts a Y t r v u := by
  unfold bpairCounts
  congr 1
  ext l
  simp [bpairCell,and_comm,and_left_comm,and_assoc]

theorem bpair_balance_contingency {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    (∀ l, l ≠ r → l ≠ t → inner ℝ (Y r) (Y l) ∈ Set.range (bContacts a) ∧
      inner ℝ (Y t) (Y l) ∈ Set.range (bContacts a)) ∧
    (∀ u, (∑ v, bpairCounts a Y r t u v)=2) ∧
    (∀ v, (∑ u, bpairCounts a Y r t u v)=2) := by
  refine ⟨bpair_remaining_types h r t hrt hB,bpairCounts_row h r t hrt hB,?_⟩
  intro v
  simp_rw [bpairCounts_swap a Y r t]
  exact bpairCounts_row h t r (Ne.symm hrt) (by rw [real_inner_comm]; exact hB) v

theorem bpair_cell_weight_sum {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (f : ℝ → ℝ → ℝ) :
    (∑ u, ∑ v, (bpairCounts a Y r t u v:ℝ)*f (bContacts a u) (bContacts a v))=
      ∑ l : Fin 8, if l ≠ r ∧ l ≠ t then f (inner ℝ (Y r) (Y l)) (inner ℝ (Y t) (Y l)) else 0 := by
  have hn (u v : Fin 3) : (bpairCounts a Y r t u v:ℝ)*f (bContacts a u) (bContacts a v)=
      ∑ l : Fin 8, if l ≠ r ∧ l ≠ t ∧ inner ℝ (Y r) (Y l)=bContacts a u ∧
        inner ℝ (Y t) (Y l)=bContacts a v then f (bContacts a u) (bContacts a v) else 0 := by
    simp [bpairCounts,bpairCell,← Finset.sum_filter]
  simp_rw [hn]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l ≠ r ∧ l ≠ t
  · obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := bpair_remaining_types h r t hrt hB l hl.1 hl.2
    rw [← hu,← hv]
    simp [hl.1,hl.2,(bContacts_injective a h.physical).eq_iff,ite_and]
  · simp [← and_assoc,hl]

end ThomsonNegative.Geometry

/- Source: N_bpair_balance/N_symmetry.lean -/

namespace ThomsonNegative.Geometry

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

end ThomsonNegative.Geometry

/- Source: N_bpair_balance/N_integer_domain.lean -/

namespace ThomsonNegative.Geometry

theorem bpair_balance_integer_domain (n : Fin 3 → Fin 3 → ℕ)
    (hsym : ∀ u v, n u v=n v u) (hrow : ∀ u, (∑ v, n u v)=2) :
    n 0 0=2-n 0 1-n 0 2 ∧ n 1 1=2-n 0 1-n 1 2 ∧ n 2 2=2-n 0 2-n 1 2 ∧
    n 0 1+n 0 2 ≤ 2 ∧ n 0 1+n 1 2 ≤ 2 ∧ n 0 2+n 1 2 ≤ 2 := by
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  rw [Fin.sum_univ_three] at h0 h1 h2
  rw [hsym 1 0] at h1
  rw [hsym 2 0,hsym 2 1] at h2
  omega

end ThomsonNegative.Geometry

/- Source: N_F/N_bpair_balance.lean -/

namespace ThomsonNegative.Geometry

theorem bpair_contact_matrix_symmetric {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    let n := bpairCounts a Y r t
    (∀ u, (∑ v, n u v)=2) ∧ (∀ v, (∑ u, n u v)=2) ∧ (∀ u v, n u v=n v u) ∧
    n 0 0=2-n 0 1-n 0 2 ∧ n 1 1=2-n 0 1-n 1 2 ∧ n 2 2=2-n 0 2-n 1 2 ∧
    n 0 1+n 0 2 ≤ 2 ∧ n 0 1+n 1 2 ≤ 2 ∧ n 0 2+n 1 2 ≤ 2 := by
  obtain ⟨_,hr,hc⟩ := bpair_balance_contingency h r t hrt hB
  have hs := bpair_balance_symmetry h h3 r t hrt hB
  exact ⟨hr,hc,hs,bpair_balance_integer_domain _ hs hr⟩

end ThomsonNegative.Geometry

/- Source: N_bpair_cases/N_eta_interval.lean -/

open Real
namespace ThomsonNegative.Geometry

def bpairU (a : ℝ) : ℝ := -3*(contacts a 0+contacts a 2)*(contacts a 0-contacts a 2)^2
def bpairV (a : ℝ) : ℝ := -3*(contacts a 0+contacts a 3)*(contacts a 0-contacts a 3)^2
def bpairW (a : ℝ) : ℝ := 12*a*(1-a)^2
def bpairEta (a : ℝ) : ℝ := -bpairU a/bpairW a

theorem bpair_UVW_identities (a : ℝ) :
    bpairU a+bpairV a=bpairW a ∧
    bpairW a= -3*(contacts a 2+contacts a 3)*(contacts a 2-contacts a 3)^2 ∧
    bpairW a=6*a*(contacts a 2-contacts a 3)^2 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  dsimp [bpairU,bpairV,bpairW,contacts]
  simp only [div_eq_mul_inv,hinv]
  refine ⟨?_,?_,?_⟩
  · linear_combination 6*a*(a-1)^2*hs
  · linear_combination -6*a*(a-1)^2*hs
  · linear_combination -6*a*(a-1)^2*hs

theorem bpair_UW_signs (a : ℝ) (ha : physical a) : bpairU a < 0 ∧ 0 < bpairW a := by
  obtain ⟨_,_,_,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  constructor
  · unfold bpairU
    have hp : 0 < contacts a 0+contacts a 2 := by linarith
    have hd : 0 < (contacts a 0-contacts a 2)^2 := sq_pos_of_pos (sub_pos.mpr hCA)
    nlinarith [mul_pos hp hd]
  · unfold bpairW
    positivity

theorem bpair_cases_eta_interval (a : ℝ) (ha : physical a) :
    bpairEta a=(contacts a 0+contacts a 2)/(2*a)*
      ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 ∧
    0 < bpairEta a ∧ bpairEta a < 1 := by
  obtain ⟨_,hDB,hB,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hCD : 0 < contacts a 2-contacts a 3 := by linarith
  have heq : bpairEta a=(contacts a 0+contacts a 2)/(2*a)*
      ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 := by
    rw [bpairEta,(bpair_UVW_identities a).2.2]
    dsimp [bpairU]
    field_simp
    ring
  have hfirst0 : 0 < (contacts a 0+contacts a 2)/(2*a) := div_pos (by linarith) (by positivity)
  have hfirst1 : (contacts a 0+contacts a 2)/(2*a) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*a)).mpr
    change a+contacts a 2 < 2*a
    change contacts a 2 < a at hCA
    linarith
  have hratio0 : 0 < (contacts a 0-contacts a 2)/(contacts a 2-contacts a 3) :=
    div_pos (sub_pos.mpr hCA) hCD
  have hCDlo : 1-a < contacts a 2-contacts a 3 := by
    have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
    have hn : √(2:ℝ) ≠ 0 := by positivity
    have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
    have hslo : 1 < √(2:ℝ) := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
    have hp := mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hslo)
    change 1-a < (-a+(1-a)/√2)-(-a-(1-a)/√2)
    simp only [div_eq_mul_inv,hinv]
    nlinarith
  have hratio1 : (contacts a 0-contacts a 2)/(contacts a 2-contacts a 3) < 1 := by
    apply (div_lt_one hCD).mpr
    change a-contacts a 2 < contacts a 2-contacts a 3
    linarith [ha.2]
  have hsquare : ((contacts a 0-contacts a 2)/(contacts a 2-contacts a 3))^2 < 1 := by nlinarith
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    exact mul_pos hfirst0 (sq_pos_of_pos hratio0)
  · rw [heq]
    nlinarith [mul_pos (sub_pos.mpr hfirst1) (sq_pos_of_pos hratio0)]

end ThomsonNegative.Geometry

/- Source: N_bpair_cases/N_cubic_equation.lean -/

namespace ThomsonNegative.Geometry

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

end ThomsonNegative.Geometry

/- Source: N_bpair_cases/N_enumeration.lean -/

namespace ThomsonNegative.Geometry

theorem bpair_cases_enumeration (i j k : ℕ) (eta : ℝ)
    (hij : i+j ≤ 2) (hik : i+k ≤ 2) (hjk : j+k ≤ 2)
    (he0 : 0 < eta) (he1 : eta < 1)
    (heq : (j:ℝ)+(k:ℝ)-2=eta*((i:ℝ)-(j:ℝ))) :
    (i=0 ∧ j=0 ∧ k=2) ∨ (i=1 ∧ j=1 ∧ k=1) := by
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num at * <;> linarith

end ThomsonNegative.Geometry

/- Source: N_F/N_bpair_cases.lean -/

namespace ThomsonNegative.Geometry

theorem bpair_two_integer_patterns {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    (bpairCounts a Y r t 0 1=0 ∧ bpairCounts a Y r t 0 2=0 ∧ bpairCounts a Y r t 1 2=2) ∨
    (bpairCounts a Y r t 0 1=1 ∧ bpairCounts a Y r t 0 2=1 ∧ bpairCounts a Y r t 1 2=1) := by
  obtain ⟨_,_,_,_,_,_,hij,hik,hjk⟩ := bpair_contact_matrix_symmetric h h3 r t hrt hB
  obtain ⟨_,hW,hUV,hc⟩ := bpair_cases_cubic_equation h h3 r t hrt hB
  obtain ⟨_,he0,he1⟩ := bpair_cases_eta_interval a h.physical
  apply bpair_cases_enumeration _ _ _ (bpairEta a) hij hik hjk he0 he1
  unfold bpairEta
  field_simp [hW.ne']
  linear_combination hc-(bpairCounts a Y r t 0 2:ℝ)*hUV

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_frame.lean -/

open Real
open ThomsonNegative.Geometry (crossVec crossVec_inner_left crossVec_inner_right crossVec_norm_sq)
namespace ThomsonNegative.Geometry

def bpairE (a : ℝ) (x z : Point) : Point := (2*√a)⁻¹ • (x+z)
def bpairF (a : ℝ) (x z : Point) : Point := (2*√(1-a))⁻¹ • (x-z)
def bpairG (a : ℝ) (x z : Point) : Point := crossVec (bpairE a x z) (bpairF a x z)
def bpairFrame (a : ℝ) (x z : Point) : Fin 3 → Point := ![bpairE a x z,bpairF a x z,bpairG a x z]

theorem bpair_frame_norms (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    ‖bpairE a x z‖=1 ∧ ‖bpairF a x z‖=1 ∧ inner ℝ (bpairE a x z) (bpairF a x z)=0 := by
  have hsa := Real.sq_sqrt ha0.le
  have hsb := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have hna : ‖x+z‖=2*√a := by
    have h := norm_add_sq_real x z
    rw [hx,hz,hB] at h
    nlinarith [norm_nonneg (x+z),Real.sqrt_nonneg a]
  have hnb : ‖x-z‖=2*√(1-a) := by
    have h := norm_sub_sq_real x z
    rw [hx,hz,hB] at h
    nlinarith [norm_nonneg (x-z),Real.sqrt_nonneg (1-a)]
  have hi : inner ℝ (x+z) (x-z)=0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,hx,hz]
    rw [real_inner_comm z x]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [bpairE,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hna]
    exact inv_mul_cancel₀ (by positivity)
  · rw [bpairF,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hnb]
    exact inv_mul_cancel₀ (by positivity)
  · simp only [bpairE,bpairF,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial,hi,mul_zero]

theorem bpairFrame_orthonormal (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    Orthonormal ℝ (bpairFrame a x z) := by
  obtain ⟨he,hf,hef⟩ := bpair_frame_norms a x z ha0 ha1 hx hz hB
  have hge : inner ℝ (bpairG a x z) (bpairE a x z)=0 := crossVec_inner_left _ _
  have hgf : inner ℝ (bpairG a x z) (bpairF a x z)=0 := crossVec_inner_right _ _
  have hg : ‖bpairG a x z‖=1 := by
    have h := crossVec_norm_sq (bpairE a x z) (bpairF a x z)
    rw [he,hf,hef] at h
    change ‖bpairG a x z‖^2 = _ at h
    nlinarith [norm_nonneg (bpairG a x z)]
  have hfe : inner ℝ (bpairF a x z) (bpairE a x z)=0 := by rw [real_inner_comm]; exact hef
  have heg : inner ℝ (bpairE a x z) (bpairG a x z)=0 := by rw [real_inner_comm]; exact hge
  have hfg : inner ℝ (bpairF a x z) (bpairG a x z)=0 := by rw [real_inner_comm]; exact hgf
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bpairFrame,Fin.ext_iff,he,hf,hg,hef,hfe,hge,heg,hgf,hfg]

def bpairOrthonormalBasis (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) : OrthonormalBasis (Fin 3) ℝ Point :=
  let hon := bpairFrame_orthonormal a x z ha0 ha1 hx hz hB
  let b := basisOfOrthonormalOfCardEqFinrank hon (by simp [Point])
  b.toOrthonormalBasis (by simpa [b] using hon)

theorem bpairOrthonormalBasis_coe (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB : Fin 3 → Point)=bpairFrame a x z := by
  simp [bpairOrthonormalBasis]

theorem exclude_six_frame (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    Orthonormal ℝ (bpairFrame a x z) ∧
    ∀ w : Point, w=inner ℝ (bpairE a x z) w • bpairE a x z+
      inner ℝ (bpairF a x z) w • bpairF a x z+inner ℝ (bpairG a x z) w • bpairG a x z := by
  refine ⟨bpairFrame_orthonormal a x z ha0 ha1 hx hz hB,?_⟩
  intro w
  have he := (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB).sum_repr' w
  rw [bpairOrthonormalBasis_coe] at he
  simpa [bpairFrame,Fin.sum_univ_succ,add_assoc] using he.symm

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_type_coordinates.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem bpair_e_coordinate (a : ℝ) (x z y : Point) :
    inner ℝ (bpairE a x z) y=(inner ℝ x y+inner ℝ z y)/(2*√a) := by
  simp only [bpairE,inner_smul_left,inner_add_left,starRingEnd_apply,star_trivial]
  ring

theorem bpair_f_coordinate (a : ℝ) (x z y : Point) :
    inner ℝ (bpairF a x z) y=(inner ℝ x y-inner ℝ z y)/(2*√(1-a)) := by
  simp only [bpairF,inner_smul_left,inner_sub_left,starRingEnd_apply,star_trivial]
  ring

theorem bpair_frame_inner (a : ℝ) (x z y w : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hB : inner ℝ x z=2*a-1) :
    inner ℝ y w=inner ℝ (bpairE a x z) y*inner ℝ (bpairE a x z) w+
      inner ℝ (bpairF a x z) y*inner ℝ (bpairF a x z) w+
      inner ℝ (bpairG a x z) y*inner ℝ (bpairG a x z) w := by
  have he := (bpairOrthonormalBasis a x z ha0 ha1 hx hz hB).sum_inner_mul_inner y w
  rw [bpairOrthonormalBasis_coe] at he
  simpa [bpairFrame,Fin.sum_univ_succ,real_inner_comm,add_assoc] using he.symm

theorem exclude_six_type_coordinates (a : ℝ) (x z y : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hB : inner ℝ x z=2*a-1)
    (alpha beta xi : ℝ) (hxy : inner ℝ x y=alpha) (hzy : inner ℝ z y=beta)
    (hxi : inner ℝ (bpairG a x z) y=xi) :
    inner ℝ (bpairE a x z) y=(alpha+beta)/(2*√a) ∧
    inner ℝ (bpairF a x z) y=(alpha-beta)/(2*√(1-a)) ∧
    ((alpha+beta)/(2*√a))^2+((alpha-beta)/(2*√(1-a)))^2+xi^2=1 := by
  have he : inner ℝ (bpairE a x z) y=(alpha+beta)/(2*√a) := by rw [bpair_e_coordinate,hxy,hzy]
  have hf : inner ℝ (bpairF a x z) y=(alpha-beta)/(2*√(1-a)) := by rw [bpair_f_coordinate,hxy,hzy]
  refine ⟨he,hf,?_⟩
  have hp := bpair_frame_inner a x z y y ha0 ha1 hx hz hB
  rw [real_inner_self_eq_norm_sq,hy,he,hf,hxi] at hp
  nlinarith

theorem bpair_reversed_coordinate_squares (a : ℝ) (x z y w : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hw : ‖w‖=1)
    (hB : inner ℝ x z=2*a-1) (alpha beta : ℝ)
    (hxy : inner ℝ x y=alpha) (hzy : inner ℝ z y=beta)
    (hxw : inner ℝ x w=beta) (hzw : inner ℝ z w=alpha) :
    (inner ℝ (bpairG a x z) y)^2=(inner ℝ (bpairG a x z) w)^2 := by
  have hyc := (exclude_six_type_coordinates a x z y ha0 ha1 hx hz hy hB alpha beta _ hxy hzy rfl).2.2
  have hwc := (exclude_six_type_coordinates a x z w ha0 ha1 hx hz hw hB beta alpha _ hxw hzw rfl).2.2
  have hplus : ((alpha+beta)/(2*√a))^2=((beta+alpha)/(2*√a))^2 := by ring
  have hminus : ((alpha-beta)/(2*√(1-a)))^2=((beta-alpha)/(2*√(1-a)))^2 := by ring
  nlinarith

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_linear_tensor_reduction.lean -/

open Real
namespace ThomsonNegative.Geometry

def sixTypes : Fin 6 → Fin 3 × Fin 3 := ![(0,1),(1,0),(0,2),(2,0),(1,2),(2,1)]
def sixU (a : ℝ) (k : Fin 6) : ℝ := bContacts a (sixTypes k).1
def sixV (a : ℝ) (k : Fin 6) : ℝ := bContacts a (sixTypes k).2
def bpairP (a : ℝ) : ℝ := (contacts a 0+contacts a 2)/(2*√a)
def sixFirst (a : ℝ) (k : Fin 6) : ℝ := (sixU a k+sixV a k)/(2*√a)
def sixSecond (a : ℝ) (k : Fin 6) : ℝ := (sixU a k-sixV a k)/(2*√(1-a))
def SixTypeNorms (a : ℝ) (xi : Fin 6 → ℝ) : Prop :=
  ∀ k, (sixFirst a k)^2+(sixSecond a k)^2+(xi k)^2=1

theorem bpairP_square (a : ℝ) (ha0 : 0 < a) : (bpairP a)^2=(1-a)^2/(8*a) := by
  have hs := Real.sq_sqrt ha0.le
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsum : contacts a 0+contacts a 2=(1-a)/√2 := by dsimp [contacts]; ring
  rw [bpairP,div_pow,hsum,div_pow,mul_pow,hs,hs2]
  ring

theorem bpairP_square_gap (a : ℝ) (ha : physical a) :
    a-(bpairP a)^2=(7*a^2+2*a-1)/(8*a) ∧ (bpairP a)^2 < a := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hpos := (contact_order_packing_bounds a ha.1 ha.2).2
  have he : a-(bpairP a)^2=(7*a^2+2*a-1)/(8*a) := by
    rw [bpairP_square a ha0]
    field_simp
    ring
  exact ⟨he,by have hp : 0 < (7*a^2+2*a-1)/(8*a) := div_pos hpos (by positivity); linarith⟩

theorem sixFirst_entries (a : ℝ) (ha0 : 0 < a) :
    sixFirst a= ![bpairP a,bpairP a,-bpairP a,-bpairP a,-√a,-√a] := by
  have hs := Real.sq_sqrt ha0.le
  have hn : √a ≠ 0 := (Real.sqrt_pos.mpr ha0).ne'
  have hCD : ((-a+(1-a)/√2)+(-a-(1-a)/√2))/(2*√a)= -√a := by
    calc
      _ = (-2*a)/(2*√a) := by congr 1; ring
      _ = _ := by field_simp; nlinarith
  funext k
  fin_cases k
  all_goals dsimp [sixFirst,sixU,sixV,sixTypes,bContacts,bContactIndex,bpairP,contacts]
  all_goals ring_nf
  all_goals field_simp
  all_goals nlinarith

theorem exclude_six_linear_tensor_reduction (a : ℝ) (ha : physical a) (xi : Fin 6 → ℝ)
    (hcent : (∑ k, xi k)=0) (hmixed : (∑ k, (sixFirst a k)^2*xi k)=0) :
    xi 4+xi 5=0 ∧ (xi 0+xi 1)+(xi 2+xi 3)=0 := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hgap := (bpairP_square_gap a ha).2
  have hs := Real.sq_sqrt ha0.le
  rw [sixFirst_entries a ha0] at hmixed
  rw [Fin.sum_univ_six] at hcent hmixed
  change (bpairP a)^2*xi 0+(bpairP a)^2*xi 1+(-bpairP a)^2*xi 2+
    (-bpairP a)^2*xi 3+(-√a)^2*xi 4+(-√a)^2*xi 5=0 at hmixed
  rw [neg_sq,neg_sq,hs] at hmixed
  have hprod : (a-(bpairP a)^2)*(xi 4+xi 5)=0 := by
    linear_combination hmixed-(bpairP a)^2*hcent
  have hz := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hgap.ne')
  exact ⟨hz,by linarith⟩

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_cubic_tensor_reduction.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem sixSecond_square_gap (a : ℝ) (ha1 : a < 1) :
    (sixSecond a 2)^2-(sixSecond a 0)^2=√2*a := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have hn : 1-a ≠ 0 := by linarith
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn2 : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  calc
    _ = ((contacts a 0-contacts a 3)^2-(contacts a 0-contacts a 2)^2)/(4*(1-a)) := by
      change ((contacts a 0-contacts a 3)/(2*√(1-a)))^2-
        ((contacts a 0-contacts a 2)/(2*√(1-a)))^2=_
      rw [div_pow,div_pow,mul_pow,hs]
      ring
    _ = _ := by
      dsimp [contacts]
      simp only [div_eq_mul_inv,hinv]
      field_simp
      ring

theorem exclude_six_cubic_tensor_reduction (a : ℝ) (ha : physical a) (xi : Fin 6 → ℝ)
    (hnorm : SixTypeNorms a xi)
    (h01 : (xi 0)^2=(xi 1)^2) (h23 : (xi 2)^2=(xi 3)^2) (h45 : (xi 4)^2=(xi 5)^2)
    (hlin3 : xi 4+xi 5=0) (hlin12 : (xi 0+xi 1)+(xi 2+xi 3)=0)
    (hcube : (∑ k, (xi k)^3)=0) :
    xi 0+xi 1=0 ∧ xi 2+xi 3=0 ∧ xi 4+xi 5=0 := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hrpos : 0 < √2*a := mul_pos (by positivity) ha0
  have hr : (xi 0)^2-(xi 2)^2=√2*a := by
    have hn0 := hnorm 0
    have hn2 := hnorm 2
    change (sixFirst a 0)^2+_+_=1 at hn0
    change (sixFirst a 2)^2+_+_=1 at hn2
    rw [sixFirst_entries a ha0] at hn0 hn2
    change (bpairP a)^2+(sixSecond a 0)^2+(xi 0)^2=1 at hn0
    change (-bpairP a)^2+(sixSecond a 2)^2+(xi 2)^2=1 at hn2
    have hg := sixSecond_square_gap a (by linarith [ha.2])
    nlinarith
  have hw : (xi 0)^2*(xi 0+xi 1)+(xi 2)^2*(xi 2+xi 3)+(xi 4)^2*(xi 4+xi 5)=0 := by
    rw [Fin.sum_univ_six] at hcube
    linear_combination hcube+xi 1*h01+xi 3*h23+xi 5*h45
  rw [hlin3,mul_zero,add_zero] at hw
  have hprod : ((xi 0)^2-(xi 2)^2)*(xi 0+xi 1)=0 := by
    linear_combination hw-(xi 2)^2*hlin12
  have hz : xi 0+xi 1=0 := (mul_eq_zero.mp hprod).resolve_left (by rw [hr]; exact hrpos.ne')
  exact ⟨hz,by linarith,hlin3⟩

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_forbidden_inner.lean -/

open Real
namespace ThomsonNegative.Geometry

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

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_realization.lean -/

open Real
namespace ThomsonNegative.Geometry

structure SixTypeRealization (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) where
  label : Fin 6 → Fin 8
  injective : Function.Injective label
  ne_r : ∀ k, label k ≠ r
  ne_t : ∀ k, label k ≠ t
  left_type : ∀ k, inner ℝ (Y r) (Y (label k))=sixU a k
  right_type : ∀ k, inner ℝ (Y t) (Y (label k))=sixV a k

theorem sixTypes_injective : Function.Injective sixTypes := by decide

theorem six_type_realization {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (h01 : bpairCounts a Y r t 0 1=1) (h02 : bpairCounts a Y r t 0 2=1)
    (h12 : bpairCounts a Y r t 1 2=1) : Nonempty (SixTypeRealization a Y r t) := by
  have hsym := bpair_balance_symmetry h h3 r t hrt hB
  have hc (k : Fin 6) : (bpairCell a Y r t (sixTypes k).1 (sixTypes k).2).Nonempty := by
    apply Finset.card_pos.mp
    have he : bpairCounts a Y r t (sixTypes k).1 (sixTypes k).2=1 := by
      fin_cases k
      · exact h01
      · exact (hsym 1 0).trans h01
      · exact h02
      · exact (hsym 2 0).trans h02
      · exact h12
      · exact (hsym 2 1).trans h12
    change 0 < bpairCounts a Y r t (sixTypes k).1 (sixTypes k).2
    omega
  choose lab hlab using hc
  have hl (k : Fin 6) := (Finset.mem_filter.mp (hlab k)).2
  refine ⟨⟨lab,?_,fun k => (hl k).1,fun k => (hl k).2.1,
    fun k => (hl k).2.2.1,fun k => (hl k).2.2.2⟩⟩
  intro i j hij
  apply sixTypes_injective
  apply Prod.ext
  · apply bContacts_injective a h.physical
    exact (hl i).2.2.1.symm.trans (by rw [hij]; exact (hl j).2.2.1)
  · apply bContacts_injective a h.physical
    exact (hl i).2.2.2.symm.trans (by rw [hij]; exact (hl j).2.2.2)

theorem SixTypeRealization.sum {a : ℝ} {Y : Fin 8 → Point} {r t : Fin 8}
    (R : SixTypeRealization a Y r t) (hrt : r ≠ t) (g : Fin 8 → ℝ) :
    (∑ l, g l)=g r+g t+∑ k, g (R.label k) := by
  classical
  have him : Finset.univ.image R.label=(Finset.univ.erase r).erase t := by
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hl
      simp [R.ne_r k,R.ne_t k]
    · rw [Finset.card_image_of_injective _ R.injective]
      simp [hrt,Ne.symm hrt]
  have he : (∑ l : Fin 8, if l ≠ r ∧ l ≠ t then g l else 0)=∑ k, g (R.label k) := by
    have hf : Finset.univ.filter (fun l : Fin 8 => l ≠ r ∧ l ≠ t)=
        (Finset.univ.erase r).erase t := by ext l; simp [and_comm]
    rw [← Finset.sum_filter,hf,← him,Finset.sum_image]
    exact fun i _ j _ hij => R.injective hij
  rw [two_indices_sum g r t hrt,he]

theorem bpair_G_endpoints (a : ℝ) (x z : Point) (ha0 : 0 < a) (ha1 : a < 1) :
    inner ℝ (bpairG a x z) x=0 ∧ inner ℝ (bpairG a x z) z=0 := by
  have hE := ThomsonNegative.Geometry.crossVec_inner_left (bpairE a x z) (bpairF a x z)
  have hF := ThomsonNegative.Geometry.crossVec_inner_right (bpairE a x z) (bpairF a x z)
  change inner ℝ (bpairG a x z) (bpairE a x z)=0 at hE
  change inner ℝ (bpairG a x z) (bpairF a x z)=0 at hF
  simp only [bpairE,inner_smul_right,inner_add_right] at hE
  simp only [bpairF,inner_smul_right,inner_sub_right] at hF
  have hnE : (2*√a)⁻¹ ≠ 0 := by positivity
  have hnF : (2*√(1-a))⁻¹ ≠ 0 := by positivity
  have he := (mul_eq_zero.mp hE).resolve_left hnE
  have hf := (mul_eq_zero.mp hF).resolve_left hnF
  exact ⟨by linarith,by linarith⟩

end ThomsonNegative.Geometry

/- Source: N_exclude_six/N_exclude.lean -/

open Real
namespace ThomsonNegative.Geometry

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


end ThomsonNegative.Geometry

/- Source: N_F/N_exclude_six.lean -/

namespace ThomsonNegative.Geometry

theorem exclude_six_contact_types {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    bpairCounts a Y r t 0 1=0 ∧ bpairCounts a Y r t 0 2=0 ∧ bpairCounts a Y r t 1 2=2 := by
  rcases bpair_two_integer_patterns h h3 r t hrt hB with hg | ⟨h01,h02,h12⟩
  · exact hg
  · exact (exclude_six_counted h h1 h3 r t hrt hB h01 h02 h12).elim

end ThomsonNegative.Geometry

/- Source: N_two_squares/N_common_A.lean -/

open Real
namespace ThomsonNegative.Geometry

structure CommonAPair (a : ℝ) (Y : Fin 8 → Point) (r t : Fin 8) where
  plus : Fin 8
  minus : Fin 8
  distinct : plus ≠ minus
  cell : bpairCell a Y r t 0 0={plus,minus}
  plus_coordinates : inner ℝ (bpairE a (Y r) (Y t)) (Y plus)=√a ∧
    inner ℝ (bpairF a (Y r) (Y t)) (Y plus)=0 ∧
    inner ℝ (bpairG a (Y r) (Y t)) (Y plus)=√(1-a)
  minus_coordinates : inner ℝ (bpairE a (Y r) (Y t)) (Y minus)=√a ∧
    inner ℝ (bpairF a (Y r) (Y t)) (Y minus)=0 ∧
    inner ℝ (bpairG a (Y r) (Y t)) (Y minus)= -√(1-a)

theorem bpair_AA_coordinates (a : ℝ) (x z y : Point) (ha0 : 0 < a) (ha1 : a < 1)
    (hx : ‖x‖=1) (hz : ‖z‖=1) (hy : ‖y‖=1) (hB : inner ℝ x z=2*a-1)
    (hxy : inner ℝ x y=a) (hzy : inner ℝ z y=a) :
    inner ℝ (bpairE a x z) y=√a ∧ inner ℝ (bpairF a x z) y=0 ∧
      (inner ℝ (bpairG a x z) y=√(1-a) ∨ inner ℝ (bpairG a x z) y= -√(1-a)) := by
  obtain ⟨he,hf,hn⟩ := exclude_six_type_coordinates a x z y ha0 ha1 hx hz hy hB a a _ hxy hzy rfl
  have hsa := Real.sq_sqrt ha0.le
  have hna : √a ≠ 0 := (Real.sqrt_pos.mpr ha0).ne'
  have hq : (a+a)/(2*√a)=√a := by field_simp; nlinarith
  rw [hq] at he hn
  simp only [sub_self,zero_div,zero_pow (by decide : 2 ≠ 0),add_zero] at hf hn
  have hsb := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have hs : (inner ℝ (bpairG a x z) y)^2=(√(1-a))^2 := by nlinarith
  exact ⟨he,hf,sq_eq_sq_iff_eq_or_eq_neg.mp hs⟩

theorem two_squares_common_A {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    (bpairCell a Y r t 0 0).card=2 ∧ Nonempty (CommonAPair a Y r t) := by
  classical
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [h.physical.1]
  have ha1 : a < 1 := by linarith [h.physical.2]
  obtain ⟨h01,h02,_⟩ := exclude_six_contact_types h h1 h3 r t hrt hB
  have hr := bpairCounts_row h r t hrt hB 0
  rw [Fin.sum_univ_three,h01,h02,add_zero,add_zero] at hr
  change (bpairCell a Y r t 0 0).card=2 at hr
  refine ⟨hr,?_⟩
  obtain ⟨u,v,huv,hcell⟩ := Finset.card_eq_two.mp hr
  have hu : u ∈ bpairCell a Y r t 0 0 := by rw [hcell]; simp
  have hv : v ∈ bpairCell a Y r t 0 0 := by rw [hcell]; simp
  have coords (k : Fin 8) (hk : k ∈ bpairCell a Y r t 0 0) :=
    bpair_AA_coordinates a (Y r) (Y t) (Y k) ha0 ha1 (h.configuration.1 r)
      (h.configuration.1 t) (h.configuration.1 k) hB
      (Finset.mem_filter.mp hk).2.2.2.1 (Finset.mem_filter.mp hk).2.2.2.2
  obtain ⟨heu,hfu,hgu⟩ := coords u hu
  obtain ⟨hev,hfv,hgv⟩ := coords v hv
  have hne : inner ℝ (bpairG a (Y r) (Y t)) (Y u) ≠
      inner ℝ (bpairG a (Y r) (Y t)) (Y v) := by
    intro he
    apply huv
    apply h.configuration.2
    have hu := (exclude_six_frame a (Y r) (Y t) ha0 ha1 (h.configuration.1 r) (h.configuration.1 t) hB).2 (Y u)
    have hv := (exclude_six_frame a (Y r) (Y t) ha0 ha1 (h.configuration.1 r) (h.configuration.1 t) hB).2 (Y v)
    rw [heu,hfu] at hu
    rw [hev,hfv] at hv
    rw [hu,hv,he]
  rcases hgu with hgu | hgu <;> rcases hgv with hgv | hgv
  · exact (hne (hgu.trans hgv.symm)).elim
  · exact ⟨⟨u,v,huv,hcell,⟨heu,hfu,hgu⟩,⟨hev,hfv,hgv⟩⟩⟩
  · refine ⟨⟨v,u,Ne.symm huv,?_,⟨hev,hfv,hgv⟩,⟨heu,hfu,hgu⟩⟩⟩
    simpa only [Finset.pair_comm] using hcell
  · exact (hne (hgu.trans hgv.symm)).elim

end ThomsonNegative.Geometry

/- Source: N_two_squares/N_square_geometry.lean -/

open Real
namespace ThomsonNegative.Geometry

/-- An actual ordered square, represented by an isometry of the target upper square. -/
structure SquareRealization (a : ℝ) (Y : Fin 8 → Point) where
  label : Fin 4 → Fin 8
  injective : Function.Injective label
  isometry : Point ≃ₗᵢ[ℝ] Point
  points : ∀ i, Y (label i)=isometry (X a (Fin.castAdd 4 i))

def SquareRealization.labels {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Finset (Fin 8) :=
  Finset.univ.image S.label

def SquareRealization.center {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Point :=
  S.isometry !₂[0,0,√a]

theorem SquareRealization.card {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    S.labels.card=4 := by simp [labels,Finset.card_image_of_injective _ S.injective]

theorem SquareRealization.gram {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : physical a) (i j : Fin 4) :
    inner ℝ (Y (S.label i)) (Y (S.label j))=
      if i=j then 1 else contacts a (candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)) := by
  rw [S.points,S.points,S.isometry.inner_map_map,candidate_gram_entry a ha]
  by_cases hij : i=j
  · subst j
    simp
  · rw [if_neg hij,if_neg (show Fin.castAdd 4 i ≠ Fin.castAdd 4 j from
      fun he => hij (Fin.ext (congrArg (fun k : Fin 8 => k.val) he)))]

def squareLocalNeighbors (i : Fin 4) (k : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => j ≠ i ∧ candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=k)

theorem squareLocalNeighbors_card (i k : Fin 4) (hk : k=0 ∨ k=1) :
    (squareLocalNeighbors i k).card=baselineCounts k := by
  have hf : ∀ i k : Fin 4, k=0 ∨ k=1 → (squareLocalNeighbors i k).card=baselineCounts k := by decide
  exact hf i k hk

theorem SquareRealization.neighbors {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (h : ContactCountData a Y) (i k : Fin 4) (hk : k=0 ∨ k=1) :
    contactNeighbors a Y (S.label i) k=(squareLocalNeighbors i k).image S.label := by
  classical
  have hsub : (squareLocalNeighbors i k).image S.label ⊆ contactNeighbors a Y (S.label i) k := by
    intro l hl
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hji,hkij⟩ := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.injective.ne hji,?_⟩
    rw [S.gram h.physical,if_neg (Ne.symm hji),hkij]
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injective _ S.injective,squareLocalNeighbors_card i k hk]
  have hc := congrFun (h.counts (S.label i)) k
  exact le_of_eq hc

theorem SquareRealization.closed_AB {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (h : ContactCountData a Y) (i j : Fin 8) (hi : i ∈ S.labels) (hij : i ≠ j)
    (hc : inner ℝ (Y i) (Y j)=contacts a 0 ∨ inner ℝ (Y i) (Y j)=contacts a 1) : j ∈ S.labels := by
  classical
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hi
  have one (k : Fin 4) (hk : k=0 ∨ k=1) (hprod : inner ℝ (Y (S.label u)) (Y j)=contacts a k) : j ∈ S.labels := by
    have hj : j ∈ contactNeighbors a Y (S.label u) k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hij,hprod⟩
    rw [S.neighbors h u k hk] at hj
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  exact hc.elim (one 0 (Or.inl rfl)) (one 1 (Or.inr rfl))

theorem SquareRealization.sum {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    (∑ i ∈ S.labels, Y i)=(4:ℝ) • S.center := by
  classical
  rw [labels,Finset.sum_image (fun i _ j _ hij => S.injective hij)]
  simp_rw [S.points]
  rw [← map_sum]
  have hs : (∑ i : Fin 4, X a (Fin.castAdd 4 i))=(4:ℝ) • (!₂[0,0,√a] : Point) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four,X] <;> ring
  rw [hs,map_smul]
  rfl

theorem SquareRealization.center_norm {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : 0 ≤ a) : ‖S.center‖^2=a := by
  rw [center,S.isometry.norm_map]
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  norm_num [Fin.sum_univ_succ,← pow_two,Real.sq_sqrt ha]

end ThomsonNegative.Geometry

/- Source: N_two_squares/N_first_square.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem square_of_common_A {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (r t : Fin 8) (hrt : r ≠ t) (hB : inner ℝ (Y r) (Y t)=contacts a 1)
    (R : CommonAPair a Y r t) :
    ∃ S : SquareRealization a Y, S.label= ![r,R.plus,t,R.minus] := by
  classical
  have hp : R.plus ∈ bpairCell a Y r t 0 0 := by rw [R.cell]; simp
  have hm : R.minus ∈ bpairCell a Y r t 0 0 := by rw [R.cell]; simp
  obtain ⟨hpr,hpt,hrp,htp⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨hmr,hmt,hrm,htm⟩ := (Finset.mem_filter.mp hm).2
  have ha := physical_mem_Ioo a h.physical
  have hpm : inner ℝ (Y R.plus) (Y R.minus)=2*a-1 := by
    have he := bpair_frame_inner a (Y r) (Y t) (Y R.plus) (Y R.minus)
      ha.1 ha.2 (h.configuration.1 r) (h.configuration.1 t) hB
    obtain ⟨hep,hfp,hgp⟩ := R.plus_coordinates
    obtain ⟨hem,hfm,hgm⟩ := R.minus_coordinates
    rw [hep,hfp,hgp,hem,hfm,hgm] at he
    have hsa := Real.sq_sqrt ha.1.le
    have hsb := Real.sq_sqrt (show 0 ≤ 1-a by linarith [ha.2])
    nlinarith
  let lab : Fin 4 → Fin 8 := ![r,R.plus,t,R.minus]
  have hinj : Function.Injective lab := by
    intro i j hij
    have hpmne := R.distinct
    fin_cases i <;> fin_cases j <;> simp_all [lab]
  have hgram := SquareTools.square_gram_of_diagonals (Y ∘ lab) a
    (fun i => h.configuration.1 _) hrp (by rw [real_inner_comm]; exact htp) htm
    (by rw [real_inner_comm]; exact hrm) hB hpm
  obtain ⟨U,hU⟩ := SquareTools.square_gram_congruent (Y ∘ lab) a ha hgram
  refine ⟨⟨lab,hinj,U,?_⟩,rfl⟩
  intro i
  exact (hU i).symm

theorem two_squares_first_square {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    ∃ S : SquareRealization a Y, S.label 0=r ∧ S.label 2=t ∧ S.labels.card=4 ∧
      (∀ i j, i ∈ S.labels → i ≠ j →
        (inner ℝ (Y i) (Y j)=contacts a 0 ∨ inner ℝ (Y i) (Y j)=contacts a 1) → j ∈ S.labels) := by
  obtain ⟨_,⟨R⟩⟩ := two_squares_common_A h h1 h3 r t hrt hB
  obtain ⟨S,hS⟩ := square_of_common_A h r t hrt hB R
  exact ⟨S,by rw [hS]; rfl,by rw [hS]; rfl,S.card,S.closed_AB h⟩

end ThomsonNegative.Geometry

/- Source: N_two_squares/N_second_square.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem SquareRealization.offdiag {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : physical a) (i j : Fin 4) (hij : i ≠ j) :
    inner ℝ (Y (S.label i)) (Y (S.label j))=contacts a 0 ∨
      inner ℝ (Y (S.label i)) (Y (S.label j))=contacts a 1 := by
  rw [S.gram ha,if_neg hij]
  have ht : ∀ i j : Fin 4, i ≠ j →
      candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=0 ∨
      candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=1 := by decide
  exact (ht i j hij).imp (congrArg (contacts a)) (congrArg (contacts a))

theorem two_squares_second_square {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) (S : SquareRealization a Y) :
    ∃ T : SquareRealization a Y, T.labels=S.labelsᶜ ∧ T.labels.card=4 ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j) ≠ contacts a 0 ∧ inner ℝ (Y i) (Y j) ≠ contacts a 1 := by
  classical
  have hcomp : S.labelsᶜ.card=4 := by rw [Finset.card_compl,S.card]; decide
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < S.labelsᶜ.card by omega)
  have hrS : r ∉ S.labels := Finset.mem_compl.mp hr
  have hbcard : (contactNeighbors a Y r 1).card=1 := congrFun (h.counts r) 1
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (contactNeighbors a Y r 1).card by omega)
  obtain ⟨htr,hB⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨T,hTr,_,_,_⟩ := two_squares_first_square h h1 h3 r t (Ne.symm htr) hB
  have hsub : T.labels ⊆ S.labelsᶜ := by
    intro l hl
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hl
    apply Finset.mem_compl.mpr
    intro hkS
    by_cases hk : k=0
    · subst k
      exact hrS (hTr ▸ hkS)
    · have hkr : T.label k ≠ r := by rw [← hTr]; exact T.injective.ne hk
      have hprod := T.offdiag h.physical k 0 hk
      rw [hTr] at hprod
      exact hrS (S.closed_AB h _ r hkS hkr hprod)
  have he : T.labels=S.labelsᶜ := Finset.eq_of_subset_of_card_le hsub (by rw [hcomp,T.card])
  refine ⟨T,he,T.card,?_⟩
  intro i hi j hj
  have hjS : j ∉ S.labels := by rw [he] at hj; exact Finset.mem_compl.mp hj
  have hij : i ≠ j := by rintro rfl; exact hjS hi
  exact ⟨fun hc => hjS (S.closed_AB h i j hi hij (Or.inl hc)),
    fun hc => hjS (S.closed_AB h i j hi hij (Or.inr hc))⟩

end ThomsonNegative.Geometry

/- Source: N_two_squares/N_opposite_centers.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem two_squares_opposite_centers {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (S T : SquareRealization a Y) (hcomp : T.labels=S.labelsᶜ) :
    T.center= -S.center ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3 := by
  classical
  have hsum := Finset.sum_add_sum_compl S.labels Y
  rw [← hcomp,S.sum,T.sum,h1] at hsum
  have hc : T.center= -S.center := by
    calc
      T.center = (1/4:ℝ) • ((4:ℝ) • S.center+(4:ℝ) • T.center)-S.center := by module
      _ = -S.center := by rw [hsum]; simp
  refine ⟨hc,?_⟩
  intro i hi j hj
  have hjS : j ∉ S.labels := by rw [hcomp] at hj; exact Finset.mem_compl.mp hj
  have hij : i ≠ j := by rintro rfl; exact hjS hi
  have hnA : inner ℝ (Y i) (Y j) ≠ contacts a 0 :=
    fun hh => hjS (S.closed_AB h i j hi hij (Or.inl hh))
  have hnB : inner ℝ (Y i) (Y j) ≠ contacts a 1 :=
    fun hh => hjS (S.closed_AB h i j hi hij (Or.inr hh))
  obtain ⟨k,hk⟩ := h.allowed_contact i j hij
  fin_cases k
  · exact (hnA hk.symm).elim
  · exact (hnB hk.symm).elim
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

end ThomsonNegative.Geometry

/- Source: N_F/N_two_squares.lean -/

namespace ThomsonNegative.Geometry

theorem recover_two_squares {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h1 : (∑ i, Y i)=0) (h3 : oddMoment 3 Y=0) :
    ∃ S T : SquareRealization a Y, T.labels=S.labelsᶜ ∧ T.center= -S.center ∧
      ‖S.center‖^2=a ∧ ‖T.center‖^2=a ∧
      ∀ i ∈ S.labels, ∀ j ∈ T.labels,
        inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3 := by
  have hbcard : (contactNeighbors a Y 0 1).card=1 := congrFun (h.counts 0) 1
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (contactNeighbors a Y 0 1).card by omega)
  obtain ⟨htr,hB⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨S,_,_,_,_⟩ := two_squares_first_square h h1 h3 0 t (Ne.symm htr) hB
  obtain ⟨T,hcomp,_,_⟩ := two_squares_second_square h h1 h3 S
  obtain ⟨hc,hcross⟩ := two_squares_opposite_centers h h1 S T hcomp
  have ha0 := (physical_mem_Ioo a h.physical).1.le
  exact ⟨S,T,hcomp,hc,S.center_norm ha0,T.center_norm ha0,hcross⟩

end ThomsonNegative.Geometry

/- Source: N_congruence/N_isometry.lean -/

namespace ThomsonNegative.Geometry

theorem congruence_isometry (v : Fin 3 → Point) (hv : Orthonormal ℝ v) :
    ∃ U : Point ≃ₗᵢ[ℝ] Point, (∀ x, U x=∑ i, x i • v i) ∧
      ∀ x i, (U.symm x) i=inner ℝ (v i) x := by
  let b := basisOfOrthonormalOfCardEqFinrank hv (by simp [Point])
  let B := b.toOrthonormalBasis (by simpa [b] using hv)
  have hB : (B : Fin 3 → Point)=v := by simp [B,b]
  refine ⟨B.repr.symm,?_,?_⟩
  · intro x
    have he := B.sum_repr_symm x
    rw [hB] at he
    exact he.symm
  · intro x i
    have he := B.repr_apply_apply x i
    rw [hB] at he
    exact he

end ThomsonNegative.Geometry

/- Source: N_congruence/N_upper_frame.lean -/

open Real
namespace ThomsonNegative.Geometry

def standardFrame : Fin 3 → Point := ![!₂[1,0,0],!₂[0,1,0],!₂[0,0,1]]

def SquareRealization.frame {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Fin 3 → Point :=
  fun i => S.isometry (standardFrame i)

theorem congruence_upper_frame {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    Orthonormal ℝ S.frame ∧ S.center=√a • S.frame 2 ∧
      (Y ∘ S.label)= ![√(1-a) • S.frame 0+√a • S.frame 2,
        √(1-a) • S.frame 1+√a • S.frame 2,
        (-√(1-a)) • S.frame 0+√a • S.frame 2,
        (-√(1-a)) • S.frame 1+√a • S.frame 2] := by
  have hs : Orthonormal ℝ standardFrame := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [standardFrame,PiLp.inner_apply,Fin.sum_univ_succ]
  refine ⟨?_,?_,?_⟩
  · rw [orthonormal_iff_ite] at hs ⊢
    intro i j
    exact (S.isometry.inner_map_map _ _).trans (hs i j)
  · change S.isometry (!₂[0,0,√a])=√a • S.isometry (!₂[0,0,1])
    rw [← map_smul]
    congr 1
    ext i
    fin_cases i <;> simp
  · funext i
    change Y (S.label i)=_
    rw [S.points]
    fin_cases i <;> dsimp [SquareRealization.frame,standardFrame,X] <;>
      rw [← map_smul,← map_smul,← map_add] <;> congr 1 <;>
      ext j <;> fin_cases j <;> simp

theorem SquareRealization.center_inner {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : 0 ≤ a) (i : Fin 8) (hi : i ∈ S.labels) : inner ℝ S.center (Y i)=a := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  rw [S.points,center,S.isometry.inner_map_map]
  fin_cases j <;> rw [PiLp.inner_apply] <;>
    norm_num [X,Fin.sum_univ_succ,← pow_two,Real.sq_sqrt ha]
  all_goals change √a*√a=a
  all_goals nlinarith [Real.sq_sqrt ha]

end ThomsonNegative.Geometry

/- Source: N_congruence/N_lower_diagonals.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem lower_axis_coordinate (a z : ℝ) (ha : a < 1)
    (hz : √(1-a)*z-a=contacts a 2 ∨ √(1-a)*z-a=contacts a 3) :
    z=√(1-a)/√2 ∨ z= -(√(1-a)/√2) := by
  have hr := Real.sqrt_pos.mpr (show 0 < 1-a by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have he : √(1-a)*(√(1-a)/√2)=(1-a)/√2 := by rw [← mul_div_assoc,← pow_two,hs]
  rcases hz with hz | hz
  · left
    apply mul_left_cancel₀ hr.ne'
    change √(1-a)*z-a= -a+(1-a)/√2 at hz
    linarith
  · right
    apply mul_left_cancel₀ hr.ne'
    change √(1-a)*z-a= -a-(1-a)/√2 at hz
    rw [mul_neg]
    linarith

theorem upper_axis_dot (a : ℝ) (y : Point) :
    inner ℝ (X a 0) y=√(1-a)*y 0+√a*y 2 ∧
      inner ℝ (X a 1) y=√(1-a)*y 1+√a*y 2 := by
  constructor <;> rw [PiLp.inner_apply] <;>
    norm_num [X,Fin.sum_univ_succ] <;> ring

theorem congruence_lower_diagonals {a : ℝ} {Y : Fin 8 → Point} (ha : physical a)
    (S T : SquareRealization a Y) (hcent : T.center= -S.center)
    (hcross : ∀ i ∈ S.labels, ∀ j ∈ T.labels,
      inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3)
    (j : Fin 8) (hj : j ∈ T.labels) :
    let y := S.isometry.symm (Y j)
    y 2= -√a ∧ (y 0=√(1-a)/√2 ∨ y 0= -(√(1-a)/√2)) ∧
      (y 1=√(1-a)/√2 ∨ y 1= -(√(1-a)/√2)) := by
  let y := S.isometry.symm (Y j)
  have haI := physical_mem_Ioo a ha
  have hc := T.center_inner haI.1.le j hj
  rw [hcent,inner_neg_left] at hc
  have he : inner ℝ S.center (Y j)=√a*y 2 := by
    change inner ℝ (S.isometry (!₂[0,0,√a])) (Y j)=_
    calc
      _ = inner ℝ (S.isometry (!₂[0,0,√a])) (S.isometry y) := by dsimp [y]; rw [S.isometry.apply_symm_apply]
      _ = _ := by rw [S.isometry.inner_map_map,PiLp.inner_apply]; norm_num [Fin.sum_univ_succ]; ring
  have hy2 : y 2= -√a := by
    apply mul_left_cancel₀ (Real.sqrt_pos.mpr haI.1).ne'
    nlinarith [Real.sq_sqrt haI.1.le]
  have he2 : √a*y 2= -a := by linarith
  have haxes (k : Fin 4) : inner ℝ (Y (S.label k)) (Y j)=inner ℝ (X a (Fin.castAdd 4 k)) y := by
    rw [S.points]
    calc
      _ = inner ℝ (S.isometry (X a (Fin.castAdd 4 k))) (S.isometry y) := by dsimp [y]; rw [S.isometry.apply_symm_apply]
      _ = _ := S.isometry.inner_map_map _ _
  have hm (k : Fin 4) : S.label k ∈ S.labels := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  have h0 := hcross _ (hm 0) j hj
  have h1 := hcross _ (hm 1) j hj
  rw [haxes 0] at h0
  rw [haxes 1] at h1
  change inner ℝ (X a 0) y=contacts a 2 ∨ inner ℝ (X a 0) y=contacts a 3 at h0
  change inner ℝ (X a 1) y=contacts a 2 ∨ inner ℝ (X a 1) y=contacts a 3 at h1
  rw [(upper_axis_dot a y).1,he2] at h0
  rw [(upper_axis_dot a y).2,he2] at h1
  exact ⟨hy2,lower_axis_coordinate a (y 0) haI.2 h0,lower_axis_coordinate a (y 1) haI.2 h1⟩

end ThomsonNegative.Geometry

/- Source: N_congruence/N_relabel.lean -/

namespace ThomsonNegative.Geometry

theorem congruence_relabel (a : ℝ) (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (U : Point ≃ₗᵢ[ℝ] Point) (hc : ∀ i, ∃ j, Y i=U (X a j)) : Congruent Y (X a) := by
  choose f hf using hc
  have hi : Function.Injective f := by
    intro i j hij
    apply hY.2
    rw [hf i,hf j,hij]
  exact ⟨U,Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,hf⟩

end ThomsonNegative.Geometry

/- Source: N_F/N_congruence.lean -/

open Real
namespace ThomsonNegative.Geometry

theorem two_squares_congruent {a : ℝ} {Y : Fin 8 → Point} (hY : IsConfiguration Y)
    (ha : physical a) (S T : SquareRealization a Y) (hcomp : T.labels=S.labelsᶜ)
    (hcent : T.center= -S.center)
    (hcross : ∀ i ∈ S.labels, ∀ j ∈ T.labels,
      inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3) :
    Congruent Y (X a) := by
  classical
  apply congruence_relabel a Y hY S.isometry
  intro j
  by_cases hj : j ∈ S.labels
  · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨Fin.castAdd 4 k,S.points k⟩
  · have hjT : j ∈ T.labels := by rw [hcomp]; exact Finset.mem_compl.mpr hj
    obtain ⟨h2,h0,h1⟩ := congruence_lower_diagonals ha S T hcent hcross j hjT
    let y := S.isometry.symm (Y j)
    have hc : ∃ k : Fin 8, y=X a k := by
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · refine ⟨4,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨7,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨5,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      · refine ⟨6,?_⟩
        ext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
    obtain ⟨k,hk⟩ := hc
    refine ⟨k,?_⟩
    calc
      Y j=S.isometry y := (S.isometry.apply_symm_apply _).symm
      _ = S.isometry (X a k) := congrArg S.isometry hk


end ThomsonNegative.Geometry
namespace ThomsonNegative.Geometry

theorem counted_moments_congruent {a : ℝ} {Y : Configuration} (h : ContactCountData a Y)
    (hodd : ∀ i,(∑ j,inner ℝ (Y i) (Y j))=0 ∧ (∑ j,(inner ℝ (Y i) (Y j))^3)=0) :
    Congruent Y (X a) := by
  obtain ⟨h1,h3⟩ := (zero_tensors_equivalence Y).mp hodd
  obtain ⟨S,T,hcomp,hcent,_,_,hcross⟩ := recover_two_squares h h1 h3
  exact two_squares_congruent h.configuration h.physical S T hcomp hcent hcross

/-- Four contacts and the first vertex moment suffice throughout the proved
negative-range height interval. The third moment is derived, not assumed. -/
theorem first_moment_congruence (a : ℝ) (Y : Configuration) (ha : physical a)
    (hlo : (5/16:ℝ) ≤ a) (hY : IsConfiguration Y) (hc : AllowedContacts a Y)
    (hm : ∀ i,(∑ j,inner ℝ (Y i) (Y j))=0) : Congruent Y (X a) := by
  have hn := vertex_counts_from_first a ha hlo Y hY hc hm
  have h3 := third_moments_from_counts a ha Y hY hc hn
  exact counted_moments_congruent ⟨ha,hY,hn⟩ (fun i => ⟨hm i,h3 i⟩)

#print axioms first_moment_congruence
end ThomsonNegative.Geometry
