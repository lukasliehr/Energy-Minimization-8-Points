import ThomsonCompact.Floor.B.Kernel
import ThomsonCompact.Packed.Comp
import Mathlib.Tactic.LinearCombination

/-!
# Soundness of the exact combination `zfin` / `zcomb` (F3b)

`zfin c F (P, Q, ns, ne, ok)` turns the exact accumulators of `Σ nᵢ Tᵢ` (`P - Q = Σ nᵢ vᵢ`, `ns ≥ Σ |nᵢ| sᵢ`,
`ne ≥ Σ |nᵢ| eᵢ`) into a packed TM of `2^-F Σ nᵢ fᵢ`: the exact signed sum modulo `2^K`, one per-slot floor shift by
`F` (F1 `round_signed` in the rounding context `mkCtx N F B W`), exact magnitudes (`pabs`), error
`⌈ne / 2^F⌉ + (N+1)`.

* `zfin_sound`: the core statement for an abstract list of terms;
* `zcomb_sound`: the kernel's accumulators `zacc` satisfy the hypotheses.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed

variable {N S B W : ℕ}

/-! ## Coefficient-list sums -/

theorem natAbs_addL_le : ∀ a b : List ℤ,
    ((addL a b).map Int.natAbs).sum ≤ (a.map Int.natAbs).sum + (b.map Int.natAbs).sum
  | [], b => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by
    have ih := natAbs_addL_le xs ys
    simp only [addL, List.map_cons, List.sum_cons]
    have := Int.natAbs_add_le x y
    omega

theorem natAbs_scaleL (n : ℤ) : ∀ a : List ℤ,
    ((scaleL n a).map Int.natAbs).sum = n.natAbs * (a.map Int.natAbs).sum
  | [] => by simp [scaleL]
  | x :: xs => by
    simp only [scaleL, List.map_cons, List.sum_cons, Int.natAbs_mul, natAbs_scaleL n xs]
    ring

theorem length_addL_le {a b : List ℤ} {m : ℕ} (ha : a.length ≤ m) (hb : b.length ≤ m) :
    (addL a b).length ≤ m := by
  rw [length_addL]; omega

/-- the combined coefficient list of a list of enclosures -/
theorem zcomb_aux (hg : Good N S B W) : ∀ (L : List (ℤ × TM × (ℝ → ℝ))),
    (∀ x ∈ L, Encl (mkCtx N S B W) x.2.1 x.2.2) →
    ∃ z : List ℤ, z.length ≤ N + 1 ∧
      horner (2 ^ W : ℤ) z % 2 ^ (W * (2 * N + 1)) =
        (L.map fun x => x.1 * (x.2.1.v : ℤ)).sum % 2 ^ (W * (2 * N + 1)) ∧
      (z.map Int.natAbs).sum ≤ (L.map fun x => x.1.natAbs * x.2.1.s).sum ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(L.map fun x => (x.1 : ℝ) * x.2.2 t).sum - evalZ z t / 2 ^ S| ≤
        (((L.map fun x => x.1.natAbs * x.2.1.e).sum : ℕ) : ℝ) / 2 ^ S
  | [], _ => ⟨[], by simp, by simp, by simp, fun t _ => by simp [evalZ]⟩
  | x :: L, hL => by
    obtain ⟨z, hz1, hz2, hz3, hz4⟩ := zcomb_aux hg L (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    obtain ⟨cs, al, hR, hf⟩ := hL x (by simp)
    refine ⟨addL (scaleL x.1 cs) z, ?_, ?_, ?_, ?_⟩
    · apply length_addL_le _ hz1
      rw [length_scaleL, hR.lcs]; simp
    · have h1 : Int.ModEq (2 ^ (W * (2 * N + 1))) (horner (2 ^ W : ℤ) cs) (x.2.1.v : ℤ) := by
        have hv := hR.hv
        simp only [mk_W, mk_K] at hv
        show _ % _ = _ % _
        rw [hv, Int.emod_emod]
      have h2 : Int.ModEq (2 ^ (W * (2 * N + 1))) (horner (2 ^ W : ℤ) z)
          (L.map fun x => x.1 * (x.2.1.v : ℤ)).sum := hz2
      have := (h1.mul_left x.1).add h2
      rw [horner_addL, horner_scaleL, List.map_cons, List.sum_cons]
      exact this
    · refine (natAbs_addL_le _ _).trans ?_
      rw [natAbs_scaleL, List.map_cons, List.sum_cons]
      have := hR.sum_natAbs_le
      have := Nat.mul_le_mul_left x.1.natAbs this
      omega
    · intro t ht
      have h1 := hf t ht
      have h2 := hz4 t ht
      simp only [mk_S] at h1
      rw [evalZ_addL, evalZ_scaleL]
      simp only [List.map_cons, List.sum_cons]
      have hD : (0 : ℝ) < 2 ^ S := by positivity
      have key : (x.1 : ℝ) * x.2.2 t + (L.map fun x => (x.1 : ℝ) * x.2.2 t).sum -
          ((x.1 : ℝ) * evalZ cs t + evalZ z t) / 2 ^ S =
          (x.1 : ℝ) * (x.2.2 t - evalZ cs t / 2 ^ S) +
            ((L.map fun x => (x.1 : ℝ) * x.2.2 t).sum - evalZ z t / 2 ^ S) := by ring
      rw [key]
      have h3 : |(x.1 : ℝ) * (x.2.2 t - evalZ cs t / 2 ^ S)| ≤ (x.1.natAbs : ℝ) * ((x.2.1.e : ℝ) / 2 ^ S) := by
        rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      calc |(x.1 : ℝ) * (x.2.2 t - evalZ cs t / 2 ^ S) +
            ((L.map fun x => (x.1 : ℝ) * x.2.2 t).sum - evalZ z t / 2 ^ S)|
          ≤ |(x.1 : ℝ) * (x.2.2 t - evalZ cs t / 2 ^ S)| +
            |(L.map fun x => (x.1 : ℝ) * x.2.2 t).sum - evalZ z t / 2 ^ S| := abs_add_le _ _
        _ ≤ (x.1.natAbs : ℝ) * ((x.2.1.e : ℝ) / 2 ^ S) +
            (((L.map fun x => x.1.natAbs * x.2.1.e).sum : ℕ) : ℝ) / 2 ^ S := add_le_add h3 h2
        _ = _ := by simp only [Nat.cast_add, Nat.cast_mul]; ring

/-! ## Exact magnitudes of a bounded digit list -/

/-- `pabs` of any packed vector whose coefficients are below `2^(W-1)` -/
theorem pabs_of_bound (hg : Good N S B W) (v : ℕ) (cs : List ℤ) (hl : cs.length = N + 1)
    (hb : ∀ x ∈ cs, |x| < 2 ^ (W - 1))
    (hv : (v : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1))) (a s e : ℕ) (ok : Bool) :
    pabs (mkCtx N S B W) ⟨v, a, s, e, ok⟩ = Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) := by
  have hW1 := hg.W1
  have hnn : ∀ x ∈ cs, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    intro x hx
    have := abs_lt.mp (hb x hx)
    constructor <;> [linarith; (rw [hH2]; linarith)]
  have hbias : (v + 2 ^ (W - 1) * ones W (N + 1)) &&& (2 ^ (W * (2 * N + 1)) - 1) =
      Nat.ofDigits (2 ^ W) (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact mod_biased hW1 (Nat.mul_le_mul_left W (by omega : N + 1 ≤ 2 * N + 1)) cs hl hb v hv
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  have hl2 : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).length = N + 1 := by simp [hl]
  have hmap : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).map (fun d => (d - 2 ^ (W - 1)) + (2 ^ (W - 1) - d)) =
      cs.map Int.natAbs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hc : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by push_cast; rfl
    have := absDigit_offset x (2 ^ (W - 1)) (by rw [hc]; exact (hnn x hx).1)
    rw [hc] at this
    exact this
  have key := pabs_ofDigits hW1 (N + 1) _ hl2 hdig
  rw [hmap, ← hbias] at key
  rw [← key]
  rfl

/-! ## The core lemma -/

theorem evalZ_zeros (l : List ℤ) (h : ∀ x ∈ l, x = 0) (t : ℝ) : evalZ l t = 0 := by
  induction l with
  | nil => simp [evalZ]
  | cons x l ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [evalZ, List.map_cons, horner_cons] at ih' ⊢
    rw [ih', hx]; simp

theorem two_pow_le_of_le {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

/-- **`zfin` soundness.** Exact accumulators of `Σ nᵢ Tᵢ` give an enclosure of `2^-F Σ nᵢ fᵢ`. -/
theorem zfin_sound (hg : Good N S B W) {F : ℕ} (hF : F + 1 ≤ W)
    (L : List (ℤ × TM × (ℝ → ℝ))) (hL : ∀ x ∈ L, Encl (mkCtx N S B W) x.2.1 x.2.2)
    (P Q ns ne : ℕ) (ok : Bool)
    (hPQ : (P : ℤ) - Q = (L.map fun x => x.1 * (x.2.1.v : ℤ)).sum)
    (hns : (L.map fun x => x.1.natAbs * x.2.1.s).sum ≤ ns)
    (hne : (L.map fun x => x.1.natAbs * x.2.1.e).sum ≤ ne)
    (hok : (zfin (mkCtx N S B W) F (P, Q, ns, ne, ok)).ok = true) :
    Encl (mkCtx N S B W) (zfin (mkCtx N S B W) F (P, Q, ns, ne, ok))
      (fun t => (L.map fun x => (x.1 : ℝ) * x.2.2 t).sum / 2 ^ F) := by
  have hgF : Good N F B W := ⟨hg.B1, hg.BW, hF, hg.NB⟩
  have hW1 := hg.W1
  obtain ⟨z0, hz1, hz2, hz3, hz4⟩ := zcomb_aux hg L hL
  -- the ok flag
  have hokE : (zfin (mkCtx N S B W) F (P, Q, ns, ne, ok)).ok =
      (ok && Nat.blt ns (2 ^ (2 * B)) && Nat.blt (zfin (mkCtx N S B W) F (P, Q, ns, ne, ok)).s (2 ^ B)) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨_, hns2⟩, hsB⟩ := hok
  -- pad to 2N+1 slots
  set z := z0 ++ List.replicate (2 * N + 1 - z0.length) 0 with hz
  have hzlen : z.length = 2 * N + 1 := by rw [hz, List.length_append, List.length_replicate]; omega
  have hzabs : (z.map Int.natAbs).sum = (z0.map Int.natAbs).sum := by
    rw [hz, List.map_append, List.sum_append]; simp
  have hzb : ∀ x ∈ z, |x| < 2 ^ (2 * B) := by
    intro x hx
    have h1 : x.natAbs ≤ (z.map Int.natAbs).sum := mem_le_sum (List.mem_map_of_mem hx)
    have h2 : x.natAbs < 2 ^ (2 * B) := by omega
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  -- the exact difference modulo 2^K (as computed by `zfin`)
  set K := W * (2 * N + 1) with hK
  set V := Nat.land (Nat.add P (Nat.sub (mkCtx N S B W).twoK (Nat.land Q (mkCtx N S B W).maskK)))
    (mkCtx N S B W).maskK with hV
  have hVz : (V : ℤ) % 2 ^ K = horner (2 ^ W : ℤ) z % 2 ^ K := by
    have hQ : Q % 2 ^ K ≤ 2 ^ K := (Nat.mod_lt _ (Nat.two_pow_pos _)).le
    have e1 : (V : ℤ) = ((P : ℤ) + (2 ^ K - ((Q : ℤ) % 2 ^ K))) % 2 ^ K := by
      show (((P + (2 ^ K - (Q &&& (2 ^ K - 1)))) &&& (2 ^ K - 1) : ℕ) : ℤ) = _
      rw [toZ_mod_mask, Nat.and_two_pow_sub_one_eq_mod]
      push_cast [Nat.cast_sub hQ]; rfl
    rw [e1, Int.emod_emod, hz, horner_append_zeros, hz2, ← hPQ]
    have hq := Int.mul_ediv_add_emod (Q : ℤ) (2 ^ K)
    rw [show (P : ℤ) + (2 ^ K - (Q : ℤ) % 2 ^ K) = ((P : ℤ) - Q) + 2 ^ K * ((Q : ℤ) / 2 ^ K + 1) by
      linear_combination -hq, Int.add_mul_emod_self_left]
  -- rounding
  have hround := round_signed hgF z hzlen hzb V (by rw [← hK]; exact hVz)
  set cs := (z.take (N + 1)).map (fun x => x / 2 ^ F) with hcs
  have hcslen : cs.length = N + 1 := by rw [hcs, List.length_map, List.length_take, hzlen]; omega
  have hcsb : ∀ x ∈ cs, |x| < 2 ^ (W - 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have h1 := hzb y (List.mem_of_mem_take hy)
    have h2 := Int.abs_ediv_le_abs y (2 ^ F)
    have h6 : (2 : ℤ) ^ (2 * B) ≤ 2 ^ (W - 1) := two_pow_le_of_le (by have := hg.BW; omega)
    linarith
  -- the result's fields
  set v := ((((V + (mkCtx N F B W).biasP) &&& (mkCtx N F B W).maskK) &&& (mkCtx N F B W).rmask) >>> F +
    (mkCtx N F B W).unb) &&& (mkCtx N F B W).maskK with hvdef
  have hvz : (v : ℤ) = horner (2 ^ W : ℤ) cs % 2 ^ K := by rw [hvdef]; exact hround
  have hvz' : (v : ℤ) % 2 ^ K = horner (2 ^ W : ℤ) cs % 2 ^ K := by rw [hvz, Int.emod_emod]
  have hpabs := pabs_of_bound hg v cs hcslen hcsb hvz' 0 0 0 true
  -- the sum of magnitudes
  have hcsabs : (cs.map Int.natAbs).sum ≤ ns + (N + 1) := by
    have h1 : ∀ (l : List ℤ), ((l.map fun x => x / 2 ^ F).map Int.natAbs).sum ≤ (l.map Int.natAbs).sum + l.length := by
      intro l
      induction l with
      | nil => simp
      | cons y l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have : (y / 2 ^ F).natAbs ≤ y.natAbs + 1 := by
          have h2 := abs_ediv_le_ceil y (2 ^ F) (Nat.two_pow_pos F) y.natAbs (by rw [Int.abs_eq_natAbs])
          have h3 : (y.natAbs + (2 ^ F - 1)) / 2 ^ F ≤ y.natAbs + 1 := by
            have := ceil_le_self F y.natAbs
            omega
          have : ((y / ((2 ^ F : ℕ) : ℤ)).natAbs : ℤ) ≤ ((y.natAbs + 1 : ℕ) : ℤ) := by
            rw [Int.natCast_natAbs]
            exact h2.trans (by exact_mod_cast h3)
          have h4 : ((2 ^ F : ℕ) : ℤ) = 2 ^ F := by push_cast; rfl
          rw [h4] at this
          exact_mod_cast this
        omega
    have h2 := h1 (z.take (N + 1))
    have h3 : ((z.take (N + 1)).map Int.natAbs).sum ≤ (z.map Int.natAbs).sum := by
      have := sum_take_le (z.map Int.natAbs) (N + 1)
      rwa [take_map'] at this
    have h4 : (z.take (N + 1)).length = N + 1 := by rw [List.length_take, hzlen]; omega
    rw [hcs]
    omega
  have hsum : (cs.map Int.natAbs).sum < 2 ^ W - 1 := by
    have := hg.pow_lt
    have := hg.NB
    omega
  have hs : ssum (mkCtx N S B W) (pabs (mkCtx N S B W) ⟨v, 0, 0, 0, true⟩) = (cs.map Int.natAbs).sum := by
    rw [hpabs]
    show Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) % (2 ^ W - 1) = _
    exact ofDigits_mod_pred (by have := hg.BW; omega) _ hsum
  -- assemble
  have hT0 : zfin (mkCtx N S B W) F (P, Q, ns, ne, ok) =
      ⟨v, pabs (mkCtx N S B W) ⟨v, 0, 0, 0, true⟩, ssum (mkCtx N S B W) (pabs (mkCtx N S B W) ⟨v, 0, 0, 0, true⟩),
        Packed.cdiv F ne + (N + 1), ok && Nat.blt ns (2 ^ (2 * B)) &&
          Nat.blt (ssum (mkCtx N S B W) (pabs (mkCtx N S B W) ⟨v, 0, 0, 0, true⟩)) (2 ^ B)⟩ := rfl
  have hT : zfin (mkCtx N S B W) F (P, Q, ns, ne, ok) =
      ⟨v, Nat.ofDigits (2 ^ W) (cs.map Int.natAbs), (cs.map Int.natAbs).sum,
        Packed.cdiv F ne + (N + 1), ok && Nat.blt ns (2 ^ (2 * B)) &&
          Nat.blt (cs.map Int.natAbs).sum (2 ^ B)⟩ := by
    rw [hT0, hs, hpabs]
  have hsB' : (cs.map Int.natAbs).sum < 2 ^ B := by
    have : (zfin (mkCtx N S B W) F (P, Q, ns, ne, ok)).s = (cs.map Int.natAbs).sum := by rw [hT]
    rw [← this]; simpa using hsB
  rw [hT]
  refine ⟨cs, cs.map Int.natAbs, ⟨hcslen, by simp [hcslen], ?_, rfl, ?_, rfl, hsB'⟩, ?_⟩
  · show (v : ℤ) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1))
    exact hvz
  · intro k
    rw [getD_map_of_zero Int.natAbs 0 0 rfl, Int.abs_eq_natAbs]
  · intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hD : (0 : ℝ) < 2 ^ S := by positivity
    have hDF : (0 : ℝ) < 2 ^ F := by positivity
    have h1 := hz4 t ht
    -- evalZ z = evalZ (take) (the rest is zero)
    have hz0 : evalZ z t = evalZ z0 t := by
      simp only [hz, evalZ, List.map_append, List.map_replicate, Int.cast_zero, horner_append_zeros]
    have htake : evalZ z t = evalZ (z.take (N + 1)) t := by
      rw [evalZ_take_drop z (N + 1) t]
      have h0 : ∀ x ∈ z.drop (N + 1), x = 0 := by
        intro x hx
        rw [hz, List.drop_append, List.drop_eq_nil_of_le (by omega : z0.length ≤ N + 1),
          List.nil_append] at hx
        exact List.eq_of_mem_replicate (List.mem_of_mem_drop hx)
      rw [evalZ_zeros _ h0, mul_zero, add_zero]
    have hr := eval_round F t hta (z.take (N + 1))
    rw [show (z.take (N + 1)).length = N + 1 by rw [List.length_take, hzlen]; omega] at hr
    have hcd := le_cdiv F ne
    have hne' : (((L.map fun x => x.1.natAbs * x.2.1.e).sum : ℕ) : ℝ) ≤ ne := by exact_mod_cast hne
    show |(L.map fun x => (x.1 : ℝ) * x.2.2 t).sum / 2 ^ F - evalZ cs t / 2 ^ S| ≤
      ((Packed.cdiv F ne + (N + 1) : ℕ) : ℝ) / 2 ^ (mkCtx N S B W).S
    simp only [mk_S]
    push_cast
    set A := (L.map fun x => (x.1 : ℝ) * x.2.2 t).sum
    have e1 : A / 2 ^ F - evalZ cs t / 2 ^ S =
        (A - evalZ z0 t / 2 ^ S) / 2 ^ F + (evalZ (z.take (N + 1)) t - 2 ^ F * evalZ cs t) / (2 ^ S * 2 ^ F) := by
      rw [← hz0, htake]; field_simp; ring
    rw [e1]
    have b1 : |(A - evalZ z0 t / 2 ^ S) / 2 ^ F| ≤ ((ne : ℝ) / 2 ^ F) / 2 ^ S := by
      rw [abs_div, abs_of_pos hDF, div_div, mul_comm, ← div_div]
      exact div_le_div_of_nonneg_right (h1.trans (div_le_div_of_nonneg_right hne' hD.le)) hDF.le
    have b2 : |(evalZ (z.take (N + 1)) t - 2 ^ F * evalZ cs t) / (2 ^ S * 2 ^ F)| ≤ ((N : ℝ) + 1) / 2 ^ S := by
      have hr' : |evalZ (z.take (N + 1)) t - 2 ^ F * evalZ cs t| ≤ ((N : ℝ) + 1) * 2 ^ F := by
        rw [hcs]; push_cast at hr; exact hr
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ S * 2 ^ F), div_le_div_iff₀ (by positivity) hD]
      calc |evalZ (z.take (N + 1)) t - 2 ^ F * evalZ cs t| * 2 ^ S ≤ ((N : ℝ) + 1) * 2 ^ F * 2 ^ S :=
            mul_le_mul_of_nonneg_right hr' hD.le
        _ = ((N : ℝ) + 1) * (2 ^ S * 2 ^ F) := by ring
    calc |(A - evalZ z0 t / 2 ^ S) / 2 ^ F + (evalZ (z.take (N + 1)) t - 2 ^ F * evalZ cs t) / (2 ^ S * 2 ^ F)|
        ≤ ((ne : ℝ) / 2 ^ F) / 2 ^ S + ((N : ℝ) + 1) / 2 ^ S := (abs_add_le _ _).trans (add_le_add b1 b2)
      _ ≤ ((Packed.cdiv F ne : ℕ) : ℝ) / 2 ^ S + ((N : ℝ) + 1) / 2 ^ S := by
          gcongr
      _ = (((Packed.cdiv F ne : ℕ) : ℝ) + ((N : ℝ) + 1)) / 2 ^ S := by ring

/-! ## The kernel accumulators -/

/-- signed value of a term -/
def tval (x : Bool × ℕ × TM) : ℤ := if x.1 then -(x.2.1 : ℤ) else x.2.1

theorem zacc_spec : ∀ (terms : List (Bool × ℕ × TM)) (P Q ns ne : ℕ) (ok : Bool),
    ((zacc terms P Q ns ne ok).1 : ℤ) - (zacc terms P Q ns ne ok).2.1 =
      (P : ℤ) - Q + (terms.map fun x => tval x * (x.2.2.v : ℤ)).sum ∧
    (zacc terms P Q ns ne ok).2.2.1 = ns + (terms.map fun x => x.2.1 * x.2.2.s).sum ∧
    (zacc terms P Q ns ne ok).2.2.2.1 = ne + (terms.map fun x => x.2.1 * x.2.2.e).sum
  | [], P, Q, ns, ne, ok => by simp [zacc]
  | x :: terms, P, Q, ns, ne, ok => by
    have ih := zacc_spec terms (cond x.1 P (Nat.add P (Nat.mul x.2.1 x.2.2.v)))
      (cond x.1 (Nat.add Q (Nat.mul x.2.1 x.2.2.v)) Q) (Nat.add ns (Nat.mul x.2.1 x.2.2.s))
      (Nat.add ne (Nat.mul x.2.1 x.2.2.e)) (and ok x.2.2.ok)
    show ((zacc terms _ _ _ _ _).1 : ℤ) - (zacc terms _ _ _ _ _).2.1 = _ ∧ (zacc terms _ _ _ _ _).2.2.1 = _ ∧
      (zacc terms _ _ _ _ _).2.2.2.1 = _
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      simp only [List.map_cons, List.sum_cons, tval]
      cases x.1 <;> simp <;> ring
    · rw [h2]; simp only [List.map_cons, List.sum_cons]; show ns + x.2.1 * x.2.2.s + _ = _; ring
    · rw [h3]; simp only [List.map_cons, List.sum_cons]; show ne + x.2.1 * x.2.2.e + _ = _; ring

/-- **`zcomb` soundness**: terms `(neg, n, T, f)` with `Encl T f` give `2^-F Σ ±n f`. -/
theorem zcomb_sound (hg : Good N S B W) {F : ℕ} (hF : F + 1 ≤ W) (L : List (Bool × ℕ × TM × (ℝ → ℝ)))
    (hL : ∀ x ∈ L, Encl (mkCtx N S B W) x.2.2.1 x.2.2.2)
    (hok : (zcomb (mkCtx N S B W) F (L.map fun x => (x.1, x.2.1, x.2.2.1))).ok = true) :
    Encl (mkCtx N S B W) (zcomb (mkCtx N S B W) F (L.map fun x => (x.1, x.2.1, x.2.2.1)))
      (fun t => (L.map fun x => (if x.1 then -(x.2.1 : ℝ) else x.2.1) * x.2.2.2 t).sum / 2 ^ F) := by
  set T3 : List (Bool × ℕ × TM) := L.map fun x => (x.1, x.2.1, x.2.2.1) with hT3
  set r := zacc T3 0 0 0 0 true with hr
  obtain ⟨h1, h2, h3⟩ := zacc_spec T3 0 0 0 0 true
  have hok' : (zfin (mkCtx N S B W) F (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2)).ok = true := hok
  have hz := zfin_sound hg hF (L.map fun x => (tval (x.1, x.2.1, x.2.2.1), x.2.2.1, x.2.2.2))
    (by intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hL x hx)
    r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
    (by rw [h1, hT3]; simp [List.map_map, Function.comp_def])
    (by
      rw [h2, zero_add, hT3]; simp only [List.map_map]
      apply le_of_eq; congr 1; apply List.map_congr_left; intro x _
      simp only [Function.comp_apply, tval]; cases x.1 <;> simp)
    (by
      rw [h3, zero_add, hT3]; simp only [List.map_map]
      apply le_of_eq; congr 1; apply List.map_congr_left; intro x _
      simp only [Function.comp_apply, tval]; cases x.1 <;> simp)
    hok'
  refine (hz.of_fields rfl rfl rfl rfl).congr (fun t _ => ?_)
  simp only [List.map_map, Function.comp_def, tval]
  congr 2
  apply List.map_congr_left
  intro x _
  cases x.1 <;> simp

end ThomsonCompact.Floor.B
