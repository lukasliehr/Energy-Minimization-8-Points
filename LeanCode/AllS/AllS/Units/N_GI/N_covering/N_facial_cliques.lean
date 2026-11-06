import AllS.Units.N_GI.N_auxiliary_graphs.N_diagonal_simple
import Lean_Code.EmptyContactSector

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_triangle_rotation (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (i : Fin 8) (q r : ContactNeighbor Y c i)
    (hqr : inner ℝ (Y q) (Y r)=c)
    (horient : 0 < inner ℝ (crossVec (Y i) (Y q)) (Y r)) :
    contactRotateAt Y c hY hc i q=r := by
  by_contra hneq
  let k := contactRotateAt Y c hY hc i q
  have htriple : 0 < inner ℝ (crossVec (Y q) (Y r)) (Y i) := by
    rwa [←triple_cyclic]
  have hlt := contactRotateAt_strict_minimal_angle Y c hY hc hirr i q r (Ne.symm hneq) htriple
  rw [equilateral_contact_angle (Y q) (Y r) c hc hqr] at hlt
  have hqk : q.val≠k.val := by
    intro heq
    have hpos := contactRotateAt_triple_pos Y c hY hc hirr i q
    change 0 < inner ℝ (crossVec (Y q) (Y k)) (Y i) at hpos
    rw [heq,triple_cyclic,crossVec_inner_left] at hpos
    exact lt_irrefl _ hpos
  have hlow := contact_angle_lower_bound (Y i) (Y q) (Y k) c
    (hY.1 _) (hY.1 _) (hY.1 _) hc q.property.2 k.property.2 (hbound q.val k.val hqk)
  exact (not_lt_of_ge hlow) hlt

theorem contact_triangle_next_tip (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (d : ContactDart Y c) (k : Fin 8)
    (hjk : inner ℝ (Y d.2.val) (Y k)=c) (hki : inner ℝ (Y k) (Y d.1)=c)
    (horient : 0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y k)) :
    (contactFaceNext Y c hY hc d).2.val=k := by
  have hkj : k≠d.2.val := by
    intro h
    rw [h,crossVec_inner_right] at horient
    exact lt_irrefl _ horient
  let q : ContactNeighbor Y c d.2.val := ⟨k,hkj,hjk⟩
  let r : ContactNeighbor Y c d.2.val := (contactReverse Y c d).2
  have hrot : contactRotateAt Y c hY hc d.2.val q=r := by
    apply contact_triangle_rotation Y c hY hc hirr hbound d.2.val q r hki
    change 0 < inner ℝ (crossVec (Y d.2.val) (Y k)) (Y d.1)
    rwa [←triple_cyclic]
  have hinv := congrArg (contactRotateAt Y c hY hc d.2.val).symm hrot
  simp only [Equiv.symm_apply_apply] at hinv
  change ((contactRotateAt Y c hY hc d.2.val).symm r).val=k
  rw [←hinv]

def triangleFaceDart {Y : Fin 8 → Point} {c : ℝ} (v : Fin 3 → Fin 8)
    (hinj : Function.Injective v)
    (hside : ∀ j, inner ℝ (Y (v j)) (Y (v (j+1)))=c) (i : Fin 3) : ContactDart Y c :=
  ⟨v i, v (i+1), (fun h => (show i+1≠i by fin_cases i <;> decide) (hinj h)), hside i⟩

theorem triangleFaceDart_next {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (v : Fin 3 → Fin 8) (hinj : Function.Injective v)
    (hside : ∀ j, inner ℝ (Y (v j)) (Y (v (j+1)))=c)
    (hturn : ∀ j, 0 < inner ℝ (crossVec (Y (v j)) (Y (v (j+1)))) (Y (v (j+1+1)))) (i : Fin 3) :
    contactFaceNext Y c hY hc (triangleFaceDart v hinj hside i)=triangleFaceDart v hinj hside (i+1) := by
  refine actual_contactDart_ext (contactFaceNext Y c hY hc (triangleFaceDart v hinj hside i))
    (triangleFaceDart v hinj hside (i+1)) rfl ?_
  apply contact_triangle_next_tip Y c hY hc hirr hbound
  · exact hside (i+1)
  · change inner ℝ (Y (v (i+1+1))) (Y (v i))=c
    have h := hside (i+1+1)
    simpa only [show i+1+1+1=i by fin_cases i <;> decide] using h
  · exact hturn i

def triangleFaceCycle {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (v : Fin 3 → Fin 8) (hinj : Function.Injective v)
    (hside : ∀ j, inner ℝ (Y (v j)) (Y (v (j+1)))=c)
    (hturn : ∀ j, 0 < inner ℝ (crossVec (Y (v j)) (Y (v (j+1)))) (Y (v (j+1+1)))) :
    ContactBoundaryCycle Y c hY hc where
  size := 2
  point := triangleFaceDart v hinj hside
  injective := fun _ _ h => hinj (congrArg Sigma.fst h)
  step := triangleFaceDart_next hY hc hirr hbound v hinj hside hturn

theorem covering_facial_cliques_oriented {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (v : Fin 3 → Fin 8) (hinj : Function.Injective v)
    (hside : ∀ j, inner ℝ (Y (v j)) (Y (v (j+1)))=c)
    (hturn : ∀ j, 0 < inner ℝ (crossVec (Y (v j)) (Y (v (j+1)))) (Y (v (j+1+1)))) :
    ∃ C : ContactBoundaryCycle Y c hY hc, C.size+1=3 ∧ Set.range C.vertex=Set.range v :=
  ⟨triangleFaceCycle hY hc hirr hbound v hinj hside hturn,rfl,rfl⟩

#print axioms covering_facial_cliques_oriented
theorem contact_triangle_triple_ne_zero (a b d : Point) (c : ℝ)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hd : ‖d‖=1) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hab : inner ℝ a b=c) (hbd : inner ℝ b d=c) (had : inner ℝ a d=c) :
    inner ℝ (crossVec a b) d ≠ 0 := by
  have hsq := contact_chain_triple_sq a b d c ha hb hd hab hbd
  rw [had] at hsq
  have h1 : 0 < 1-c := by linarith [hc.2]
  have h2 : 0 < 1+c-2*c^2 := by
    have hm := mul_pos h1 (show 0<1+2*c by linarith [hc.1])
    nlinarith
  intro hz
  rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hsq
  have hh := mul_pos h1 h2
  linarith

theorem triangle_all_turns_of_positive (Y : Fin 8 → Point) (v : Fin 3 → Fin 8)
    (hpos : 0 < inner ℝ (crossVec (Y (v 0)) (Y (v 1))) (Y (v 2))) :
    ∀ j, 0 < inner ℝ (crossVec (Y (v j)) (Y (v (j+1)))) (Y (v (j+1+1))) := by
  intro j
  have hj : j=0 ∨ j=1 ∨ j=2 := by fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl
  · exact hpos
  · change 0 < inner ℝ (crossVec (Y (v 1)) (Y (v 2))) (Y (v 0))
    rwa [←triple_cyclic]
  · change 0 < inner ℝ (crossVec (Y (v 2)) (Y (v 0))) (Y (v 1))
    rwa [triple_cyclic]

theorem covering_facial_cliques {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (v : Fin 3 → Fin 8) (hinj : Function.Injective v)
    (hcontact : ∀ i j, i≠j → inner ℝ (Y (v i)) (Y (v j))=c) :
    ∃ C : ContactBoundaryCycle Y c hY hc, C.size+1=3 ∧ Set.range C.vertex=Set.range v := by
  have hn := contact_triangle_triple_ne_zero (Y (v 0)) (Y (v 1)) (Y (v 2)) c
    (hY.1 _) (hY.1 _) (hY.1 _) hc (hcontact 0 1 (by decide))
    (hcontact 1 2 (by decide)) (hcontact 0 2 (by decide))
  by_cases hp : 0 < inner ℝ (crossVec (Y (v 0)) (Y (v 1))) (Y (v 2))
  · apply covering_facial_cliques_oriented hY hc hirr hbound v hinj
    · exact fun j => hcontact j (j+1) (by fin_cases j <;> decide)
    · exact triangle_all_turns_of_positive Y v hp
  · let e := Equiv.swap (1:Fin 3) 2
    let w : Fin 3 → Fin 8 := fun j => v (e j)
    have hw : Function.Injective w := hinj.comp e.injective
    have hwside (j : Fin 3) : inner ℝ (Y (w j)) (Y (w (j+1)))=c :=
      hcontact (e j) (e (j+1)) (fun h => (show j≠j+1 by fin_cases j <;> decide) (e.injective h))
    have hwpos : 0 < inner ℝ (crossVec (Y (w 0)) (Y (w 1))) (Y (w 2)) := by
      change 0 < inner ℝ (crossVec (Y (v 0)) (Y (v 2))) (Y (v 1))
      rw [triple_swap_last]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hn)
    obtain ⟨C,hC,hr⟩ := covering_facial_cliques_oriented hY hc hirr hbound w hw hwside
      (triangle_all_turns_of_positive Y w hwpos)
    refine ⟨C,hC,hr.trans ?_⟩
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨e j,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e.symm j,congrArg v (e.apply_symm_apply j)⟩

#print axioms covering_facial_cliques

end Blueprint.Thomson.Tail.Implementation
