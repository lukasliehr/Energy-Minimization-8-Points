import ThomsonCompact.Target.Core
import ThomsonCompact.Packed.Comp

/-!
# Internal order (milestone T3): soundness of `liftTo` and `truncTo`

The target pipeline runs at order `N + dN` and is truncated once at the end (`Core.lean`):
`liftTo_sound` embeds an order-`N` TM into the order-`N₂` context (`N ≤ N₂`, same `S B W`, same polynomial and error),
`truncTo_sound` truncates an order-`N₂` TM to order `N`, the exact tail `Σ_{k>N} |cₖ|` moving into the error.
-/

namespace ThomsonCompact.Target
open ThomsonCompact.Packed

theorem getD_append_zeros {α : Type*} [Zero α] : ∀ (L : List α) (n k : ℕ),
    (L ++ List.replicate n 0).getD k 0 = L.getD k 0
  | [], 0, k => by simp
  | [], n + 1, 0 => by simp [List.replicate_succ]
  | [], n + 1, k + 1 => by
    rw [List.nil_append, List.replicate_succ, List.getD_cons_succ]
    have := getD_append_zeros ([] : List α) n k
    simpa using this
  | x :: L, n, 0 => by simp
  | x :: L, n, k + 1 => by
    rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_append_zeros L n k

theorem dom_natAbs (z : List ℤ) : Dom z (z.map Int.natAbs) := by
  intro k
  have : (z.map Int.natAbs).getD k 0 = (z.getD k 0).natAbs := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases z[k]? <;> rfl
  rw [this, Int.abs_eq_natAbs]

/-- re-centring biased digits: `ofDigits (zₖ + 2^(W-1)) + (2^K - 2^(W-1)·Σ_{k<n} 2^(Wk))`, reduced modulo `2^K`, is the
residue of `Σ zₖ 2^(Wk)` -/
theorem rebias {W K n : ℕ} (hW : 1 ≤ W) (hK : W * n ≤ K) (z : List ℤ) (hz : z.length = n)
    (hnn : ∀ x ∈ z, 0 ≤ x + 2 ^ (W - 1)) :
    (((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) + (2 ^ K - 2 ^ (W - 1) * ones W n)) &&&
      (2 ^ K - 1) : ℕ) : ℤ) = horner (2 ^ W : ℤ) z % 2 ^ K := by
  have hcast := cast_ofDigits_offset (W := W) (by omega) (2 ^ (W - 1)) z hnn
  rw [hz] at hcast
  have hhb : 2 ^ (W - 1) * ones W n < 2 ^ K := by
    have h1 : 2 ^ (W - 1) * ones W n = Nat.ofDigits (2 ^ W) (List.replicate n (2 ^ (W - 1))) := by
      rw [ofDigits_replicate (by omega)]
    have h2 : Nat.ofDigits (2 ^ W) (List.replicate n (2 ^ (W - 1))) < 2 ^ (W * n) := by
      have := ofDigits_lt_pow (W := W) (by omega) (List.replicate n (2 ^ (W - 1))) (by
        intro d hd
        rw [List.eq_of_mem_replicate hd]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega))
      simpa using this
    rw [h1]
    exact h2.trans_le (Nat.pow_le_pow_right (by norm_num) hK)
  have e1 : ((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) +
      (2 ^ K - 2 ^ (W - 1) * ones W n) : ℕ) : ℤ) = horner (2 ^ W : ℤ) z + 2 ^ K := by
    rw [Nat.cast_add, Nat.cast_sub hhb.le, hcast]
    push_cast
    ring
  rw [Nat.and_two_pow_sub_one_eq_mod]
  calc (((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) + (2 ^ K - 2 ^ (W - 1) * ones W n)) %
        2 ^ K : ℕ) : ℤ)
      = ((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) +
          (2 ^ K - 2 ^ (W - 1) * ones W n) : ℕ) : ℤ) % 2 ^ K := by push_cast; rfl
    _ = (horner (2 ^ W : ℤ) z + 2 ^ K) % 2 ^ K := by rw [e1]
    _ = horner (2 ^ W : ℤ) z % 2 ^ K := Int.add_emod_right _ _

/-- an order-`N` TM is an order-`N₂` TM with the same polynomial and error -/
theorem liftTo_sound {N N2 S B W : ℕ} (hg : Good N S B W) (hN : N ≤ N2) {A : TM} {f : ℝ → ℝ}
    (hA : Encl (mkCtx N S B W) A f) :
    Encl (mkCtx N2 S B W) (liftTo (mkCtx N S B W) (mkCtx N2 S B W) A) f := by
  obtain ⟨cs, al, hR, hf⟩ := hA
  obtain ⟨hbias, hnn⟩ := hR.biased hg
  have hlen : cs.length = N + 1 := hR.lcs
  have hlal : al.length = N + 1 := hR.lal
  have hW1 := hg.W1
  refine ⟨cs ++ List.replicate (N2 - N) 0, al ++ List.replicate (N2 - N) 0,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.length_append, List.length_replicate, mk_m, hlen]; omega
  · simp only [List.length_append, List.length_replicate, mk_m, hlal]; omega
  · show (((((A.v + 2 ^ (W - 1) * ones W (N + 1)) &&& (2 ^ (W * (2 * N + 1)) - 1)) +
        (2 ^ (W * (2 * N2 + 1)) - 2 ^ (W - 1) * ones W (N + 1))) &&& (2 ^ (W * (2 * N2 + 1)) - 1) : ℕ) : ℤ) =
      horner (2 ^ W : ℤ) (cs ++ List.replicate (N2 - N) 0) % 2 ^ (W * (2 * N2 + 1))
    rw [hbias, horner_append_zeros]
    exact rebias hW1 (by nlinarith) cs hlen (fun x hx => (hnn x hx).1)
  · have hha : A.a = Nat.ofDigits (2 ^ W) al := hR.ha
    show A.a = Nat.ofDigits (2 ^ W) (al ++ List.replicate (N2 - N) 0)
    rw [hha, Nat.ofDigits_append, ofDigits_replicate (W := W) (by omega), zero_mul, mul_zero, add_zero]
  · intro k
    rw [getD_append_zeros, getD_append_zeros]
    exact hR.dom k
  · show A.s = _
    rw [hR.hs, List.sum_append, List.sum_replicate, smul_zero, add_zero]
  · show A.s < 2 ^ B
    exact hR.sB
  · intro t ht
    show |f t - evalZ (cs ++ List.replicate (N2 - N) 0) t / 2 ^ S| ≤ (A.e : ℝ) / 2 ^ S
    have h := hf t ht
    rw [evalZ, List.map_append, List.map_replicate, Int.cast_zero, horner_append_zeros]
    exact h

/-- an order-`N₂` TM truncated to order `N ≤ N₂`: same low coefficients, exact magnitudes, the exact tail
`Σ_{k>N} |cₖ|` added to the error -/
theorem truncTo_sound {N N2 S B W : ℕ} (hg2 : Good N2 S B W) (hN : N ≤ N2) (g : Bool) {T : TM} {f : ℝ → ℝ}
    (hT : Encl (mkCtx N2 S B W) T f) :
    Encl (mkCtx N S B W) (truncTo (mkCtx N2 S B W) (mkCtx N S B W) g T) f := by
  obtain ⟨cs, al, hR, hf⟩ := hT
  obtain ⟨hbias, hnn⟩ := hR.biased hg2
  have hlen : cs.length = N2 + 1 := hR.lcs
  have hW1 := hg2.W1
  have hBW := hg2.BW
  have hP := hR.pabs_eq hg2
  -- digit bounds
  have hsum := hR.sum_natAbs_le
  have hsB : T.s < 2 ^ B := hR.sB
  have h2B : 2 ^ B < 2 ^ W - 1 := by
    have h4 : 2 ^ (B + 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (B + 2) = 4 * 2 ^ B := by rw [pow_add]; ring
    have h6 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
    omega
  have hdigA : ∀ d ∈ cs.map Int.natAbs, d < 2 ^ W := by
    intro d hd
    have := List.le_sum_of_mem hd
    omega
  have hsplitA := ofDigits_take_drop (by omega) (cs.map Int.natAbs) hdigA (N + 1)
  have hdigB := offset_digits_lt (2 ^ (W - 1)) hnn
  have hsplitB := ofDigits_take_drop (by omega) _ hdigB (N + 1)
  have htd := List.sum_take_add_sum_drop (cs.map Int.natAbs) (N + 1)
  have hlt1 : ((cs.take (N + 1)).length) = N + 1 := by rw [List.length_take]; omega
  have ha : Nat.land (pabs (mkCtx N2 S B W) T) (mkCtx N S B W).maskWm =
      Nat.ofDigits (2 ^ W) ((cs.take (N + 1)).map Int.natAbs) := by
    show pabs (mkCtx N2 S B W) T &&& (2 ^ (W * (N + 1)) - 1) = _
    rw [hP, Nat.and_two_pow_sub_one_eq_mod, hsplitA.1, List.map_take]
  have htail : ssum (mkCtx N2 S B W) (Nat.shiftRight (pabs (mkCtx N2 S B W) T) (mkCtx N S B W).wm) =
      ((cs.drop (N + 1)).map Int.natAbs).sum := by
    show (pabs (mkCtx N2 S B W) T >>> (W * (N + 1))) % (2 ^ W - 1) = _
    rw [hP, Nat.shiftRight_eq_div_pow, hsplitA.2, ← List.map_drop]
    exact ofDigits_mod_pred (by omega) _ (by rw [List.map_drop]; omega)
  have hlow : ((cs.take (N + 1)).map Int.natAbs).sum < 2 ^ B := by
    rw [List.map_take]; omega
  refine ⟨cs.take (N + 1), (cs.take (N + 1)).map Int.natAbs, ⟨?_, ?_, ?_, ?_, dom_natAbs _, ?_, ?_⟩, ?_⟩
  · simpa using hlt1
  · simpa using hlt1
  · show ((((((T.v + 2 ^ (W - 1) * ones W (N2 + 1)) &&& (2 ^ (W * (2 * N2 + 1)) - 1)) &&&
        (2 ^ (W * (N + 1)) - 1)) + (2 ^ (W * (2 * N + 1)) - 2 ^ (W - 1) * ones W (N + 1))) &&&
        (2 ^ (W * (2 * N + 1)) - 1) : ℕ) : ℤ) = horner (2 ^ W : ℤ) (cs.take (N + 1)) % 2 ^ (W * (2 * N + 1))
    rw [hbias, Nat.and_two_pow_sub_one_eq_mod (Nat.ofDigits _ _), hsplitB.1, ← List.map_take]
    exact rebias hW1 (by nlinarith) (cs.take (N + 1)) hlt1 (fun x hx => (hnn x (List.mem_of_mem_take hx)).1)
  · exact ha
  · show Nat.land (pabs (mkCtx N2 S B W) T) (mkCtx N S B W).maskWm % (2 ^ W - 1) = _
    rw [ha]
    exact ofDigits_mod_pred (by omega) _ (by omega)
  · show Nat.land (pabs (mkCtx N2 S B W) T) (mkCtx N S B W).maskWm % (2 ^ W - 1) < 2 ^ B
    rw [ha, ofDigits_mod_pred (by omega) _ (by omega)]
    exact hlow
  · intro t ht
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have h1 := hf t ht
    have hsplit : evalZ cs t = evalZ (cs.take (N + 1)) t + t ^ (N + 1) * evalZ (cs.drop (N + 1)) t := by
      simp only [evalZ]
      rw [horner_take_drop t (N + 1) (cs.map (Int.cast : ℤ → ℝ)), List.map_take, List.map_drop]
    have h2 := abs_evalZ_le (dom_natAbs (cs.drop (N + 1))) t ht'
    have h3 : |t ^ (N + 1)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) ht'
    have h4 : |t ^ (N + 1) * evalZ (cs.drop (N + 1)) t| ≤ (((cs.drop (N + 1)).map Int.natAbs).sum : ℝ) := by
      rw [abs_mul]
      calc |t ^ (N + 1)| * |evalZ (cs.drop (N + 1)) t| ≤ 1 * |evalZ (cs.drop (N + 1)) t| := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2
    show |f t - evalZ (cs.take (N + 1)) t / 2 ^ S| ≤
      ((Nat.add T.e (ssum (mkCtx N2 S B W) (Nat.shiftRight (pabs (mkCtx N2 S B W) T) (mkCtx N S B W).wm)) : ℕ) : ℝ) /
        2 ^ S
    rw [htail]
    have hS : (0 : ℝ) < 2 ^ S := by positivity
    have e : f t - evalZ (cs.take (N + 1)) t / 2 ^ S =
        (f t - evalZ cs t / 2 ^ S) + (t ^ (N + 1) * evalZ (cs.drop (N + 1)) t) / 2 ^ S := by
      rw [hsplit]; ring
    rw [e, show ((Nat.add T.e ((cs.drop (N + 1)).map Int.natAbs).sum : ℕ) : ℝ) =
      (T.e : ℝ) + (((cs.drop (N + 1)).map Int.natAbs).sum : ℝ) from Nat.cast_add _ _, add_div]
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right h4 hS.le

#print axioms liftTo_sound
#print axioms truncTo_sound

end ThomsonCompact.Target
