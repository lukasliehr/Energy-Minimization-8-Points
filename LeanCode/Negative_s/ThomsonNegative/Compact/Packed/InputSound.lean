import ThomsonNegative.Compact.Packed.Input
import ThomsonNegative.Compact.Packed.Comp

noncomputable section
namespace ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

theorem digitsN_pad {W : ℕ} (m : ℕ) (L : List ℕ) (hL : L.length≤m)
    (hd : ∀ d ∈ L, d<2^W) :
    digitsN W m (Nat.ofDigits (2^W) L)=L++List.replicate (m-L.length) 0 := by
  have hd' : ∀ d ∈ L++List.replicate (m-L.length) 0, d<2^W := by
    intro d hdm
    rcases List.mem_append.mp hdm with h | h
    · exact hd d h
    · rw [List.eq_of_mem_replicate h]; positivity
  have hlen : (L++List.replicate (m-L.length) 0).length=m := by simp; omega
  have hval : Nat.ofDigits (2^W) (L++List.replicate (m-L.length) 0)=Nat.ofDigits (2^W) L := by
    rw [Nat.ofDigits_append,Nat.ofDigits_replicate_zero,mul_zero,add_zero]
  have h := digitsN_ofDigits (W:=W) _ hd'
  rwa [hlen,hval] at h

theorem zipWith_sub_zeros (k : ℕ) :
    List.zipWith (fun p q : ℕ => (p:ℤ)-(q:ℤ)) (List.replicate k 0) (List.replicate k 0)=
      List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.zipWith_cons_cons,ih]; simp

theorem affineInput_zero_sound (hg : Good N S B W) (a0 a1 : ℕ)
    (h0 : a0<2^W) (h1 : a1<2^W) (hN : 1≤N)
    (hok : (affineInput (mkCtx N S B W) a0 a1 0).ok=true) :
    Encl (mkCtx N S B W) (affineInput (mkCtx N S B W) a0 a1 0)
      (fun t => ((a0:ℝ)+a1*t)/2^S) := by
  have h := ofPQ_sound hg (Nat.add a0 (Nat.shiftLeft a1 W)) 0 0 hok
  refine h.congr (fun t _ => ?_)
  have hp : Nat.add a0 (Nat.shiftLeft a1 W)=Nat.ofDigits (2^W) [a0,a1] := by
    simp [Nat.ofDigits_cons,Nat.shiftLeft_eq]; ring
  have hz : (0:ℕ)=Nat.ofDigits (2^W) [0,0] := by simp [Nat.ofDigits_cons]
  have hQd : digitsN W (N+1) 0=[0,0]++List.replicate (N-1) 0 := by
    calc
      _ = digitsN W (N+1) (Nat.ofDigits (2^W) [0,0]) := congrArg (digitsN W (N+1)) hz
      _ = _ := by
        rw [digitsN_pad (N+1) _ (by simp; omega) (by simp [Nat.two_pow_pos])]
        simp only [List.length_cons,List.length_nil]
        rw [show N+1-(0+1+1)=N-1 by omega]
  have hc : pqCoeffs W (N+1) (Nat.add a0 (Nat.shiftLeft a1 W)) 0=
      (a0:ℤ)::(a1:ℤ)::List.replicate (N-1) 0 := by
    unfold pqCoeffs
    rw [hp,digitsN_pad (N+1) _ (by simp; omega) (by simp [h0,h1])]
    rw [hQd]
    simp only [List.length_cons,List.length_nil]
    rw [show N+1-(0+1+1)=N-1 by omega]
    simp only [List.cons_append,List.nil_append,List.zipWith_cons_cons,Int.natCast_zero,sub_zero,
      zipWith_sub_zeros]
  rw [hc]
  simp only [evalZ,List.map_cons,horner_cons,List.map_replicate,Int.cast_zero]
  rw [horner_replicate_zero]
  push_cast
  ring

theorem affineInput_sound (hg : Good N S B W) (a0 a1 e0 e1 : ℕ) (a b : ℝ)
    (h0 : a0<2^W) (h1 : a1<2^W) (hN : 1≤N)
    (ha : |a-(a0:ℝ)/2^S| ≤ (e0:ℝ)/2^S)
    (hb : |b-(a1:ℝ)/2^S| ≤ (e1:ℝ)/2^S)
    (hok : (affineInput (mkCtx N S B W) a0 a1 (e0+e1)).ok=true) :
    Encl (mkCtx N S B W) (affineInput (mkCtx N S B W) a0 a1 (e0+e1)) (fun t => a+b*t) := by
  have h := affineInput_zero_sound hg a0 a1 h0 h1 hN hok
  have hw := widen_sound (e0+e1) h (g:=fun t => a+b*t) (by
    intro t ht
    have ht' : |t|≤1 := abs_le.mpr ht
    have hE : a+b*t-((a0:ℝ)+a1*t)/2^S=(a-(a0:ℝ)/2^S)+(b-(a1:ℝ)/2^S)*t := by ring
    rw [hE]
    calc
      _ ≤ |a-(a0:ℝ)/2^S|+|(b-(a1:ℝ)/2^S)*t| := abs_add_le _ _
      _ ≤ (e0:ℝ)/2^S+(e1:ℝ)/2^S := by
        rw [abs_mul]
        have hh := mul_le_mul hb ht' (abs_nonneg t) (by positivity : (0:ℝ)≤e1/2^S)
        nlinarith
      _ = _ := by simp only [mk_S]; push_cast; ring)
  exact hw.of_fields rfl rfl rfl (by simp [widen,affineInput,ofPQ])

theorem ofPQ_poly_sound (hg : Good N S B W) (P Q e : ℕ)
    (hok : (ofPQ (mkCtx N S B W) P Q e).ok=true) :
    Encl (mkCtx N S B W) (ofPQ (mkCtx N S B W) P Q e)
      (poly (mkCtx N S B W) (ofPQ (mkCtx N S B W) P Q e)) := by
  obtain ⟨cs,al,hR,_⟩ := ofPQ_sound hg P Q e hok
  exact (Encl.self hR).congr (fun t _ => by rw [poly,hR.decode_eq hg])

#print axioms affineInput_sound
#print axioms ofPQ_poly_sound
end ThomsonNegative.Compact.Packed
