import AllS.Units.N_FI.N_exclude_six.N_forbidden_inner

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

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
  have hE := SquareAntiprismVerification.crossVec_inner_left (bpairE a x z) (bpairF a x z)
  have hF := SquareAntiprismVerification.crossVec_inner_right (bpairE a x z) (bpairF a x z)
  change inner ℝ (bpairG a x z) (bpairE a x z)=0 at hE
  change inner ℝ (bpairG a x z) (bpairF a x z)=0 at hF
  simp only [bpairE,inner_smul_right,inner_add_right] at hE
  simp only [bpairF,inner_smul_right,inner_sub_right] at hF
  have hnE : (2*√a)⁻¹ ≠ 0 := by positivity
  have hnF : (2*√(1-a))⁻¹ ≠ 0 := by positivity
  have he := (mul_eq_zero.mp hE).resolve_left hnE
  have hf := (mul_eq_zero.mp hF).resolve_left hnF
  exact ⟨by linarith,by linarith⟩

#print axioms six_type_realization
#print axioms SixTypeRealization.sum
#print axioms bpair_G_endpoints
end Blueprint.Thomson.Finite
