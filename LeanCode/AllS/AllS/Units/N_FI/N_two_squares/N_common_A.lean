import AllS.Units.N_F.N_exclude_six

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

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

#check two_squares_common_A
#print axioms two_squares_common_A
end Blueprint.Thomson.Finite
