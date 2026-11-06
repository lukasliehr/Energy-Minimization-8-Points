import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.StageZSound

/-!
# Soundness of the re-centred records (F2i)

* `shiftH_eval`: the exact homogeneous Taylor shift, `Σ ρⱼ (2^k y - m)ʲ = 2^(k (n-1)) Σ wᵢ yⁱ`;
* `cmpShift_eval`, `bodyShiftOk_eval`: a checked shifted body evaluates at `y - m/2^k` (divided by its scale) to the
  original body at `y`;
* `rfRec_shift`, `shift_facts`: the one-time checks give `(LS.rfRec i).value (y - m/2^k) = (L.rfRec i).value y` for
  every record `i < nRec` (no side condition: a vanishing denominator vanishes on both sides);
* `blockRowC_ok`, `blockRowC_good`: the re-centred rows enclose the **same** real rows `L.blockRowF a b` as `blockRow`;
* `pLookC_sound`, `zStageOkC_spec` (`ZFactsC`, `join_v`, `join_i`, `full`), `PSC_sound`: the `P` lookups with the
  re-centred rows enclose the same real `P` table `pLF` as `pLook_sound` / `PS_sound` (stage Z may use another
  Gram lookup than stage P).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

variable {N S B W : ℕ}

/-! ## The exact Taylor shift -/

/-- Real evaluation `Σ wᵢ uⁱ` of a `ℕ` coefficient list. -/
noncomputable def evalN (w : List ℕ) (u : ℝ) : ℝ := horner u (w.map (Nat.cast : ℕ → ℝ))

@[simp] theorem evalN_nil (u : ℝ) : evalN [] u = 0 := rfl

@[simp] theorem evalN_cons (x : ℕ) (w : List ℕ) (u : ℝ) : evalN (x :: w) u = x + u * evalN w u := rfl

theorem mulLin_eval (m : ℕ) (u : ℝ) : ∀ (r : List ℕ) (p : ℕ), evalN (mulLin m r p) u = p + (m + u) * evalN r u
  | [], p => by
    show evalN [p] u = _
    simp
  | x :: xs, p => by
    show evalN (Nat.add (Nat.mul m x) p :: mulLin m xs x) u = _
    rw [evalN_cons, mulLin_eval m u xs x, evalN_cons, Nat.add_eq, Nat.mul_eq]
    push_cast
    ring

theorem addHead_eval (a : ℕ) (u : ℝ) : ∀ (r : List ℕ), evalN (addHead a r) u = a + evalN r u
  | [] => by
    show evalN [a] u = _
    simp
  | x :: xs => by
    show evalN (Nat.add a x :: xs) u = _
    rw [evalN_cons, evalN_cons, Nat.add_eq]
    push_cast
    ring

theorem shiftH_snd (m k : ℕ) : ∀ (w : List ℕ), (shiftH m k w).2 = 2 ^ (k * w.length)
  | [] => rfl
  | x :: xs => by
    show Nat.shiftLeft (shiftH m k xs).2 k = _
    rw [shiftH_snd m k xs, shl_eq, List.length_cons, Nat.mul_succ, pow_add]

theorem shiftH_cons (m k x : ℕ) (xs : List ℕ) :
    (shiftH m k (x :: xs)).1 = addHead (Nat.mul x (shiftH m k xs).2) (mulLin m (shiftH m k xs).1 0) := rfl

/-- **The exact homogeneous Taylor shift**: `Σⱼ ρⱼ (2^k y - m)ʲ = 2^(k (n-1)) Σᵢ wᵢ yⁱ` (`n = len w ≥ 1`). -/
theorem shiftH_eval (m k : ℕ) (y : ℝ) :
    ∀ (w : List ℕ), w ≠ [] → evalN (shiftH m k w).1 (2 ^ k * y - m) = 2 ^ (k * (w.length - 1)) * evalN w y
  | [], h => absurd rfl h
  | [x], _ => by
    rw [shiftH_cons, addHead_eval, mulLin_eval]
    show ((Nat.mul x 1 : ℕ) : ℝ) + ((0 : ℕ) + ((m : ℝ) + (2 ^ k * y - m)) * evalN [] (2 ^ k * y - m)) = _
    simp
  | x :: y' :: rest, _ => by
    have ih := shiftH_eval m k y (y' :: rest) (List.cons_ne_nil _ _)
    rw [shiftH_cons, addHead_eval, mulLin_eval, ih, shiftH_snd]
    have e1 : k * ((x :: y' :: rest).length - 1) = k * (y' :: rest).length := by simp
    have e2 : k * (y' :: rest).length = k * ((y' :: rest).length - 1) + k := by
      simp only [List.length_cons]; rw [Nat.add_sub_cancel, Nat.mul_succ]
    rw [e1, Nat.mul_eq, evalN_cons (x := x)]
    push_cast
    rw [e2, pow_add]
    ring

/-! ## Checked shifted bodies -/

theorem posW_sub_negW (w v : ℕ) : ((posW w v : ℤ) - (negW w v : ℤ)) = unbiasW w v := by
  unfold posW negW unbiasW
  generalize Nat.shiftLeft 1 (Nat.sub w 1) = H
  rw [Int.subNatNat_eq_coe]
  show ((v - H : ℕ) : ℤ) - ((H - v : ℕ) : ℤ) = (v : ℤ) - H
  omega

theorem evalZ_cons' (z : ℤ) (zs : List ℤ) (t : ℝ) : evalZ (z :: zs) t = z + t * evalZ zs t := by
  simp [evalZ, horner]

theorem evalZ_nil' (t : ℝ) : evalZ [] t = 0 := by simp [evalZ, horner]

/-- The decoded body is the difference of its positive and negative parts. -/
theorem evalZ_body (w : ℕ) (y : ℝ) : ∀ (b : List ℕ),
    evalZ (b.map (unbiasW w)) y = evalN (b.map (posW w)) y - evalN (b.map (negW w)) y
  | [] => by simp [evalZ_nil']
  | v :: bs => by
    rw [List.map_cons, evalZ_cons', evalZ_body w y bs, List.map_cons, List.map_cons, evalN_cons, evalN_cons]
    have h := posW_sub_negW w v
    have h' : ((unbiasW w v : ℤ) : ℝ) = (posW w v : ℝ) - (negW w v : ℝ) := by
      rw [← h]; push_cast; ring
    rw [h']
    ring

theorem cmpShift_eval (w' k : ℕ) : ∀ (b' : List ℕ) (rp rn : List ℕ) (pw : ℕ) (t : ℝ),
    cmpShift w' k b' rp rn pw = true →
      evalZ (b'.map (unbiasW w')) t = pw * (evalN rp (2 ^ k * t) - evalN rn (2 ^ k * t))
  | [], rp, rn, pw, t, h => by
    have h' : (rp.isEmpty && rn.isEmpty) = true := h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h'
    obtain ⟨rfl, rfl⟩ := h'
    simp [evalZ_nil']
  | s :: bs, rp, rn, pw, t, h => by
    cases rp with
    | nil => exact absurd h (by simp [cmpShift])
    | cons p rp' =>
      cases rn with
      | nil => exact absurd h (by simp [cmpShift])
      | cons q rn' =>
        have h' : (Nat.beq (Nat.add s (Nat.mul q pw)) (Nat.add (Nat.mul p pw) (Nat.shiftLeft 1 (Nat.sub w' 1))) &&
            cmpShift w' k bs rp' rn' (Nat.shiftLeft pw k)) = true := h
        rw [Bool.and_eq_true, Nat.beq_eq] at h'
        obtain ⟨h1, h2⟩ := h'
        have ih := cmpShift_eval w' k bs rp' rn' (Nat.shiftLeft pw k) t h2
        have hs : ((unbiasW w' s : ℤ) : ℝ) = (p : ℝ) * pw - (q : ℝ) * pw := by
          unfold unbiasW
          rw [Int.subNatNat_eq_coe]
          have h1' : (s : ℤ) + q * pw = p * pw + (Nat.shiftLeft 1 (Nat.sub w' 1) : ℕ) := by exact_mod_cast h1
          have : ((s : ℤ) - (Nat.shiftLeft 1 (Nat.sub w' 1) : ℕ)) = p * pw - q * pw := by linarith
          rw [this]; push_cast; ring
        rw [List.map_cons, evalZ_cons', hs, ih, evalN_cons, evalN_cons, shl_eq]
        push_cast
        ring

/-- **A checked shifted body** evaluates at `y - m/2^k` (over its scale) to the original body at `y`. -/
theorem bodyShiftOk_eval {m k w w' : ℕ} {b b' : List ℕ} {M M' : ℕ} (h : bodyShiftOk m k w w' b b' M M' = true)
    (y : ℝ) : evalZ (b'.map (unbiasW w')) (y - m / 2 ^ k) / M' = evalZ (b.map (unbiasW w)) y / M := by
  unfold bodyShiftOk at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hsc, hc⟩ := h
  have hE := cmpShift_eval w' k b' _ _ 1 (y - m / 2 ^ k) hc
  have h2k : (2 : ℝ) ^ k * (y - m / 2 ^ k) = 2 ^ k * y - m := by
    have : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  rw [h2k] at hE
  rcases b with _ | ⟨v, bs⟩
  · -- empty body: both sides vanish
    have h0 : (shiftH m k ([] : List ℕ)).1 = [] := rfl
    simp only [List.map_nil, h0, evalN_nil, sub_zero, mul_zero] at hE
    rw [hE, zero_div, List.map_nil, evalZ_nil', zero_div]
  · have hne : (v :: bs).map (posW w) ≠ [] := by simp
    have hne' : (v :: bs).map (negW w) ≠ [] := by simp
    rw [shiftH_eval m k y _ hne, shiftH_eval m k y _ hne'] at hE
    simp only [List.length_map] at hE
    have hsc' : Nat.shiftLeft M' k = M * (shiftH m k ((v :: bs).map (posW w))).2 := by
      simp only [List.isEmpty_cons, Bool.false_or, Nat.beq_eq] at hsc
      exact hsc
    rw [shiftH_snd, List.length_map, shl_eq] at hsc'
    set n := (v :: bs).length with hn
    have hn1 : n = (n - 1) + 1 := by rw [hn]; simp
    have hM : (M' : ℝ) = M * 2 ^ (k * (n - 1)) := by
      have h3 : (M' : ℝ) * 2 ^ k = M * 2 ^ (k * n) := by exact_mod_cast hsc'
      have e : k * n = k * (n - 1) + k := by
        conv_lhs => rw [hn1]
        ring
      have h4 : (2 : ℝ) ^ (k * n) = 2 ^ (k * (n - 1)) * 2 ^ k := by rw [e, pow_add]
      rw [h4] at h3
      exact mul_right_cancel₀ (show (2 : ℝ) ^ k ≠ 0 by positivity) (by rw [h3]; ring)
    rw [hE, hM, evalZ_body w y (v :: bs)]
    simp only [Nat.cast_one, one_mul]
    rw [← mul_sub]
    have hp : (2 : ℝ) ^ (k * (n - 1)) ≠ 0 := by positivity
    rw [mul_comm (M : ℝ), ← div_div, mul_div_cancel_left₀ _ hp]

namespace DegD

theorem recShiftOk_parts (L LS : DegD) {m k i : ℕ} (hr : L.recShiftOk LS m k i = true) :
    LS.denIdx i = L.denIdx i ∧ L.denIdx i < L.nDen ∧
      bodyShiftOk m k L.rfW LS.rfW (((L.recSlots i).drop 3).take ((L.recSlots i).getD 0 0))
        (((LS.recSlots i).drop 3).take ((LS.recSlots i).getD 0 0)) ((L.recSlots i).getD 1 1)
        ((LS.recSlots i).getD 1 1) = true := by
  unfold recShiftOk at hr
  dsimp only at hr
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hr
  exact ⟨hr.1.1, hr.1.2, hr.2⟩

/-- **A checked shifted record** has the same value at `y - m/2^k` as the original record at `y`. -/
theorem rfRec_shift (L LS : DegD) {m k i : ℕ} (hr : L.recShiftOk LS m k i = true)
    (hd : L.denShiftOk LS m k (L.denIdx i) = true) (y : ℝ) :
    (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y := by
  obtain ⟨hidx', -, hb⟩ := recShiftOk_parts L LS hr
  unfold denShiftOk at hd
  dsimp only at hd
  have hn := bodyShiftOk_eval hb y
  have hdn := bodyShiftOk_eval hd y
  unfold RFRec.value DegD.rfRec
  dsimp only
  rw [hidx']
  unfold DegD.numZ DegD.numS DegD.denZ DegD.denS
  dsimp only
  rw [hn, hdn]

/-- One-time leaf spec: the records `[k0, k1)`. -/
theorem recShiftRange_spec (L LS : DegD) {m k k0 k1 : ℕ} (h : L.recShiftRange LS m k k0 k1 = true) :
    ∀ i, k0 ≤ i → i < k1 → L.recShiftOk LS m k i = true := by
  intro i h0 h1
  unfold recShiftRange at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr h1)
  rw [show Nat.ble k0 i = true from Nat.ble_eq.mpr h0] at this
  simpa using this

/-- One-time leaf spec: all shared denominators. -/
theorem denShiftAll_spec (L LS : DegD) {m k : ℕ} (h : L.denShiftAll LS m k = true) :
    ∀ d, d < L.nDen → L.denShiftOk LS m k d = true := by
  intro d hd
  unfold denShiftAll at h
  rw [List.all_eq_true] at h
  exact h d (List.mem_range.mpr hd)

/-- **The per-degree shift facts** from the one-time leaves. -/
theorem shift_facts (L LS : DegD) {m k : ℕ} (hR : ∀ i, i < L.nRec → L.recShiftOk LS m k i = true)
    (hD : L.denShiftAll LS m k = true) :
    ∀ i, i < L.nRec → ∀ y : ℝ, (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y :=
  fun i hi y => rfRec_shift L LS (hR i hi)
    (denShiftAll_spec L LS hD _ (recShiftOk_parts L LS (hR i hi)).2.1) y

end DegD

/-! ## Rows -/

theorem shT_encl (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (m k : ℕ) (hk : k ≤ S)
    (hok : (shT (mkCtx N S B W) m k A).ok = true) :
    Encl (mkCtx N S B W) (shT (mkCtx N S B W) m k A) (fun t => a t - m / 2 ^ k) := by
  have h := addC_sound hA true (Nat.shiftLeft m (Nat.sub (mkCtx N S B W).S k)) 0 (-(m / 2 ^ k : ℝ))
    (by
      have hS : (mkCtx N S B W).S = S := rfl
      rw [hS, if_pos rfl, shl_eq]
      have e : ((m * 2 ^ (Nat.sub S k) : ℕ) : ℝ) / 2 ^ S = m / 2 ^ k := by
        push_cast
        have : (2 : ℝ) ^ S = 2 ^ (Nat.sub S k) * 2 ^ k := by
          rw [← pow_add]; congr 1; show S = S - k + k; omega
        rw [this]
        field_simp
      rw [neg_div, e]
      simp)
    hok hg
  exact (refresh_sound hg h).congr (fun t _ => by ring)

namespace DegD

variable (L : DegD)

theorem scalarRowC_ok (LS : DegD) (hg : Good N S B W) {A T : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (m k : ℕ) (hT : Encl (mkCtx N S B W) T (fun t => a t - m / 2 ^ k))
    (hsh : ∀ i, i < L.nRec → ∀ y : ℝ, (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y)
    (h0 : ∀ y, (L.rfRec 0).value y = 1) (j u : ℕ) :
    RowOk (mkCtx N S B W) (L.scalarRowC LS (mkCtx N S B W) A T j u) (L.scalarRowF a j u) := by
  unfold RowOk DegD.scalarRowC DegD.scalarRowF
  refine forall₂_map_same _ (fun i _ => ⟨rfl, ?_⟩)
  by_cases hc : L.colRec j i u = 0
  · have hb : Nat.beq (L.colRec j i u) 0 = true := by rw [hc]; rfl
    simp only [hb, if_true, EntryOk]
    intro t _
    rw [hc, h0]
  · have hb : Nat.beq (L.colRec j i u) 0 = false :=
      Bool.eq_false_iff.mpr (fun h => hc (Nat.eq_of_beq_eq_true h))
    simp only [hb, Bool.false_eq_true, if_false, EntryOk]
    by_cases hr : L.colRec j i u < L.nRec
    · rw [show Nat.blt (L.colRec j i u) L.nRec = true from Nat.blt_eq.mpr hr, cond_true]
      exact (recTMr_sound LS hg hT _).congr (fun t _ => hsh _ hr (a t))
    · rw [show Nat.blt (L.colRec j i u) L.nRec = false from
        Bool.eq_false_iff.mpr (fun h => hr (Nat.blt_eq.mp h)), cond_false]
      exact recTMr_sound L hg hA _

/-- **The re-centred rows enclose the real rows of `blockRow`.** -/
theorem blockRowC_ok (LS : DegD) (m k : ℕ) (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (hA : Encl (mkCtx N S B W) A a)
    (hsh : ∀ i, i < L.nRec → ∀ y : ℝ, (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y)
    (h0 : ∀ y, (L.rfRec 0).value y = 1) (b : ℕ)
    (hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ ∀ j, j ≤ L.gdim b → qAllZero (mP b j).s = true) (u : ℕ) :
    RowOk (mkCtx N S B W) (L.blockRowC LS m k (mkCtx N S B W) A b u) (L.blockRowF a b u) := by
  by_cases hb : b < L.dH
  · have h := blockRow_ok L hg hA h0 b hmom u
    unfold DegD.blockRow at h
    unfold DegD.blockRowC
    rw [if_pos hb] at h ⊢
    exact h
  · unfold DegD.blockRowC DegD.blockRowF
    rw [if_neg hb, if_neg hb]
    cases hc : (Nat.ble k (mkCtx N S B W).S && (shT (mkCtx N S B W) m k A).ok) with
    | true =>
      rw [Bool.and_eq_true] at hc
      have hk : k ≤ S := Nat.ble_eq.mp hc.1
      exact scalarRowC_ok L LS hg hA m k (shT_encl hg hA m k hk hc.2) hsh h0 _ u
    | false =>
      exact scalarRowr_ok L hg hA h0 _ u

theorem blockRowC_good (LS : DegD) (m k : ℕ) (c : Ctx) (A : TM) (b : ℕ)
    (hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ L.rdim b = L.gdim b + 1) (u : ℕ) (hu : u < L.rdim b) :
    RowGood (L.gdim b) (L.blockRowC LS m k c A b u) := by
  by_cases hb : b < L.dH
  · have h := blockRow_good L c A b hmom u hu
    unfold DegD.blockRow at h
    unfold DegD.blockRowC
    rw [if_pos hb] at h ⊢
    exact h
  · unfold DegD.blockRowC
    rw [if_neg hb]
    cases hc : (Nat.ble k c.S && (shT c m k A).ok) with
    | false =>
      have h := blockRow_good L c A b (fun h => absurd h hb) u hu
      unfold DegD.blockRow at h
      rw [if_neg hb] at h
      exact h
    | true =>
      simp only [cond_true]
      unfold DegD.scalarRowC RowGood
      have hjb : Nat.add L.dH (b - L.dH) = b := by show L.dH + (b - L.dH) = b; omega
      refine ⟨?_, ?_⟩
      · rw [List.map_map]
        have h1 := (List.pairwise_lt_range (n := L.gdim (Nat.add L.dH (b - L.dH)))).filter
          (fun i => !(Nat.beq (L.colRec (b - L.dH) i u) 1))
        simpa [Function.comp_def] using h1
      · intro p hp'
        simp only [List.mem_map, List.mem_filter, List.mem_range] at hp'
        obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hp'
        rw [hjb] at hi
        exact hi

end DegD

/-! ## The single-stage lookup -/

theorem pTC_lookup (L LS : DegD) (m k : ℕ) (c : Ctx) (A : TM) (WT : ℕ → ℕ → TM) (b u v : ℕ) :
    L.pLookC LS m k c A WT b u v =
      if u < L.rdim b ∧ v < L.rdim b then
        pTMD c (L.blockRowC LS m k c A b)
          (zColsD c (L.blockRowC LS m k c A b) (wRowsD WT (L.gdim b)) (L.gdim b) (L.rdim b)) u v
      else zeroTM := by
  unfold DegD.pLookC DegD.pTC pTabD
  by_cases hu : u < L.rdim b
  · rw [listAt_mkList _ _ hu]
    by_cases hv : v < L.rdim b
    · rw [listAt_mkList _ _ hv, if_pos ⟨hu, hv⟩]
    · rw [listAt_mkList_ge _ _ (Nat.le_of_not_lt hv), if_neg (fun h => hv h.2)]
  · rw [listAt_mkList_ge _ _ (Nat.le_of_not_lt hu), if_neg (fun h => hu h.1)]
    rfl

/-- **The single-stage lookup with re-centred rows encloses the real `P` table.** -/
theorem pLookC_sound (L LS : DegD) (m k : ℕ) (hg : Good N S B W) {A : TM} {WT : ℕ → ℕ → TM}
    {Wf : ℕ → ℕ → ℝ → ℝ} {rowF : ℕ → List (ℕ × (ℝ → ℝ))} (b : ℕ)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j))
    (hrow : ∀ u, RowOk (mkCtx N S B W) (L.blockRowC LS m k (mkCtx N S B W) A b u) (rowF u))
    (hgood : ∀ u, u < L.rdim b → RowGood (L.gdim b) (L.blockRowC LS m k (mkCtx N S B W) A b u))
    (hWsym : ∀ i j, WT i j = WT j i) (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t) (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.pLookC LS m k (mkCtx N S B W) A WT b u v) (pLF Wf rowF (L.rdim b) u v) := by
  rw [pTC_lookup]
  by_cases h : u < L.rdim b ∧ v < L.rdim b
  · rw [if_pos h]
    exact (pTMD_sound hg hW hrow hgood hWsym hWs h.1 h.2).congr (fun t _ => by unfold pLF; rw [if_pos h])
  · rw [if_neg h]
    exact zero_enclOk.congr (fun t _ => by unfold pLF; rw [if_neg h])

/-! ## Stage Z / stage P -/

/-- The stage-Z facts of the re-centred rows (`ZFacts`). -/
def ZFactsC (L LS : DegD) (m k : ℕ) (c : Ctx) (A : TM) (WT : ℕ → ℕ → TM) (zd : ZData) (b v0 v1 i0 i1 : ℕ) :
    Prop :=
  ∀ v, v0 ≤ v → v < v1 → v < L.rdim b → pivotOf (L.blockRowC LS m k c A b v) = none →
    ∀ i, i0 ≤ i → i < i1 → i < L.gdim b →
      L.zOk1 c zd b i v (zTMD c (L.blockRowC LS m k c A b) (wRowsD WT (L.gdim b)) i v) = true

/-- **Stage-Z leaf spec** (re-centred rows). -/
theorem zStageOkC_spec (L LS : DegD) {m k : ℕ} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData}
    {b v0 v1 i0 i1 : ℕ} (h : L.zStageOkC LS m k c A WT zd b v0 v1 i0 i1 = true) :
    ZFactsC L LS m k c A WT zd b v0 v1 i0 i1 := by
  intro v hv0 hv1 hvn hp i hi0 hi1 hin
  unfold DegD.zStageOkC at h
  rw [List.all_eq_true] at h
  have h1 := h v (List.mem_range.mpr hvn)
  have hb1 : (Nat.ble v0 v && Nat.blt v v1) = true := by
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hv0, hv1⟩
  rw [hb1, hp] at h1
  dsimp only at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 i hin
  have hb2 : (Nat.ble i0 i && Nat.blt i i1) = true := by
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hi0, hi1⟩
  rw [hb2] at h2
  simpa using h2

theorem ZFactsC.join_v {L LS : DegD} {m k : ℕ} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData}
    {b v0 v1 v2 i0 i1 : ℕ} (h1 : ZFactsC L LS m k c A WT zd b v0 v1 i0 i1)
    (h2 : ZFactsC L LS m k c A WT zd b v1 v2 i0 i1) : ZFactsC L LS m k c A WT zd b v0 v2 i0 i1 := by
  intro v hv0 hv2 hvn hp i hi0 hi1 hin
  by_cases hv : v < v1
  · exact h1 v hv0 hv hvn hp i hi0 hi1 hin
  · exact h2 v (by omega) hv2 hvn hp i hi0 hi1 hin

theorem ZFactsC.join_i {L LS : DegD} {m k : ℕ} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData}
    {b v0 v1 i0 i1 i2 : ℕ} (h1 : ZFactsC L LS m k c A WT zd b v0 v1 i0 i1)
    (h2 : ZFactsC L LS m k c A WT zd b v0 v1 i1 i2) : ZFactsC L LS m k c A WT zd b v0 v1 i0 i2 := by
  intro v hv0 hv1 hvn hp i hi0 hi2 hin
  by_cases hi : i < i1
  · exact h1 v hv0 hv1 hvn hp i hi0 hi hin
  · exact h2 v hv0 hv1 hvn hp i (by omega) hi2 hin

theorem ZFactsC.full {L LS : DegD} {m k : ℕ} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData} {b v1 i1 : ℕ}
    (h : ZFactsC L LS m k c A WT zd b 0 v1 0 i1) (hv : L.rdim b ≤ v1) (hi : L.gdim b ≤ i1) :
    ∀ v, v < L.rdim b → pivotOf (L.blockRowC LS m k c A b v) = none → ∀ i, i < L.gdim b →
      L.zOk1 c zd b i v (zTMD c (L.blockRowC LS m k c A b) (wRowsD WT (L.gdim b)) i v) = true :=
  fun v hvn hp i hin => h v (Nat.zero_le _) (by omega) hvn hp i (Nat.zero_le _) (by omega) hin

section PSC

variable (L LS : DegD) (m k : ℕ) (hg : Good N S B W) {A : TM} {WTz WTp : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
  {rowF : ℕ → List (ℕ × (ℝ → ℝ))} (zd : ZData) (b : ℕ)
  (hWz : ∀ i j, EnclOk (mkCtx N S B W) (WTz i j) (Wf i j))
  (hWp : ∀ i j, EnclOk (mkCtx N S B W) (WTp i j) (Wf i j))
  (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t)
  (hrow : ∀ u, RowOk (mkCtx N S B W) (L.blockRowC LS m k (mkCtx N S B W) A b u) (rowF u))
  (hgood : ∀ u, u < L.rdim b → RowGood (L.gdim b) (L.blockRowC LS m k (mkCtx N S B W) A b u))
  (hz : ∀ v, v < L.rdim b → pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b v) = none → ∀ i, i < L.gdim b →
    L.zOk1 (mkCtx N S B W) zd b i v
      (zTMD (mkCtx N S B W) (L.blockRowC LS m k (mkCtx N S B W) A b) (wRowsD WTz (L.gdim b)) i v) = true)
include hg hWz hWp hWs hrow hgood hz

theorem zDecC_sound {i w : ℕ} (hi : i < L.gdim b) (hw : w < L.rdim b)
    (hp : pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b w) = none) :
    EnclOk (mkCtx N S B W) (L.zDec (mkCtx N S B W) zd b i w) (zF Wf rowF i w) :=
  zDec_encl hg L zd b i w (zTMD_sound hg hWz hrow hgood hi hw) (hz w hw hp i hi)

/-- The tabled entry `pSBC u v` encloses the real `P u v` (inside the block). -/
theorem pSBC_sound {u v : ℕ} (huv : u < L.rdim b ∧ v < L.rdim b) :
    EnclOk (mkCtx N S B W) (L.pSBC LS m k (mkCtx N S B W) A WTp zd b u v) (pF Wf rowF u v) := by
  unfold DegD.pSBC
  cases hpu : pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b u) with
  | none =>
    cases hpv : pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b v) with
    | none =>
      show EnclOk _ (dotOpt _ (zipRow (L.blockRowC LS m k _ A b v)
        (mkList (fun i => L.zDec _ zd b i u) (L.gdim b)) 0)) _
      rw [zipRow_full (hgood v huv.2)]
      refine (dotRow_sound hg hWz hrow hgood huv.2 (fun i => L.zDec _ zd b i u) (fun i => zF Wf rowF i u)
        (fun i hi => zDecC_sound L LS m k hg zd b hWz hWp hWs hrow hgood hz hi huv.1 hpu)).congr
        (fun t ht => ?_)
      rw [pF_symm hWs u v t ht]
      rfl
    | some j =>
      show EnclOk _ (L.zDec _ zd b j u) _
      obtain ⟨κ, hrf, hκ⟩ := rowF_pivot (hrow v) hpv
      have hgv := hgood v huv.2
      rw [pivotOf_some hpv] at hgv
      have hj : j < L.gdim b := hgv.2 _ (List.mem_singleton_self _)
      refine (zDecC_sound L LS m k hg zd b hWz hWp hWs hrow hgood hz hj huv.1 hpu).congr (fun t ht => ?_)
      unfold zF pF
      apply congrArg List.sum
      apply List.map_congr_left
      intro q _
      rw [show zF Wf rowF q.1 v t = Wf q.1 j t from zF_pivot hrf hκ q.1 t ht, hWs _ _ t ht]
  | some i =>
    obtain ⟨κu, hrfu, hκu⟩ := rowF_pivot (hrow u) hpu
    have hgu := hgood u huv.1
    rw [pivotOf_some hpu] at hgu
    have hi : i < L.gdim b := hgu.2 _ (List.mem_singleton_self _)
    cases hpv : pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b v) with
    | none =>
      show EnclOk _ (L.zDec _ zd b i v) _
      refine (zDecC_sound L LS m k hg zd b hWz hWp hWs hrow hgood hz hi huv.2 hpv).congr (fun t ht => ?_)
      rw [pF_pivot hrfu hκu v t ht]
    | some j =>
      show EnclOk _ (WTp j i) _
      obtain ⟨κv, hrfv, hκv⟩ := rowF_pivot (hrow v) hpv
      refine (hWp j i).congr (fun t ht => ?_)
      rw [pF_pivot hrfu hκu v t ht, zF_pivot hrfv hκv i t ht, hWs _ _ t ht]

/-- **The stage-P lookup with re-centred rows encloses the real `P` table** (stage-Z facts with `WTz`, pivot-pivot
entries from `WTp`). -/
theorem PSC_sound (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.PSC LS m k (mkCtx N S B W) A WTp zd b u v) (pLF Wf rowF (L.rdim b) u v) := by
  unfold DegD.PSC DegD.pTSC
  by_cases huv : u < L.rdim b ∧ v < L.rdim b
  · rw [listAt_mkList _ _ huv.2, listAt_mkList _ _ huv.1]
    exact (pSBC_sound L LS m k hg zd b hWz hWp hWs hrow hgood hz huv).congr
      (fun t _ => by unfold pLF; rw [if_pos huv])
  · have hz0 : listAt zeroTM (listAt [] (mkList (fun v => mkList (fun u => L.pSBC LS m k (mkCtx N S B W) A WTp zd b u v)
        (L.rdim b)) (L.rdim b)) v) u = zeroTM := by
      by_cases hv : v < L.rdim b
      · rw [listAt_mkList _ _ hv, listAt_mkList_ge _ _ (by omega)]
      · rw [listAt_mkList_ge _ _ (by omega)]; rfl
    rw [hz0]
    exact zero_enclOk.congr (fun t _ => by unfold pLF; rw [if_neg huv])

end PSC

#print axioms DegD.shift_facts
#print axioms DegD.blockRowC_ok
#print axioms pLookC_sound
#print axioms zStageOkC_spec
#print axioms PSC_sound

end ThomsonCompact.CoeffMap.Deg
