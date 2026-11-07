import ThomsonCompact.Floor.B.SoundRowT

/-!
# Soundness of the channel leaf (F3b)

The channel leaf `chanOk` checks the stored control parts `cvc` against the centre numerals and bounds the channel
values; `chanAll` builds the full channel vectors from them.

* `chanZ cb m`: the integer channel vector of coordinate `m`: the Bernstein controls `z_i = Σ_k C_k β̃_ik`
  (`β̃ = D β`, `D = bernDen N`) of the centre numeral `cm m`, then the target direction `±qn` in slot `N+1+dirT m`;
* `chanZc cb m`: `chanZ cb m` on the stored coordinates `m < cvc.length` (`= nin`, checked), zero beyond
  (`ChanSem.bnd` quantifies over all `m`, the leaf bounds the coordinates `m < nin` only);
* `chanOk_sound`: `ChanSem cb (chanAll … cvc 0) (chanZc cb)`: the stored control part is `Σ_k C_k bcol_k ≡
  Σ_i z_i 2^(WC i) mod 2^M` (`chanCtl_mod`), `|z_i| ≤ cmax` (`ctl_abs_le`), hence a valid `M`-bit two's complement
  numeral, sign-extended to `KC` bits (`sgnExt_mod`) plus the direction (`addDir_mod`);
* `chanOk_facts`: the scalar facts of the leaf used by the row theorem;
* `sv_bernI`, `chooseF_eq`, `chooseF_dvd_bernDen`, `bernDen_pos`: the arithmetic of `β̃` (for `SoundChanOld`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

/-! ## The channel vectors -/

/-- the integer channel vector of coordinate `m`: Bernstein controls (scaled by `D`) of the centre numerals,
then the target direction -/
noncomputable def chanZ (cb : CellB) (m : ℕ) : List ℤ :=
  (List.range (cb.N + 1)).map (fun i => ∑ k ∈ Finset.range (cb.N + 1),
      sv (smDec (slot cb.wc (cb.cm m) k)) * sv (bernI cb.N cb.D i k)) ++
    (List.range cb.nT).map (fun tt => if cb.dirT m = tt then sv (cb.dirQ m) else 0)

/-- `chanZ` on the stored coordinates `m < cvc.length`, zero beyond -/
noncomputable def chanZc (cb : CellB) (m : ℕ) : List ℤ := if m < cb.cvc.length then chanZ cb m else List.replicate cb.nC 0

theorem chanZc_of_lt (cb : CellB) {m : ℕ} (hm : m < cb.cvc.length) : chanZc cb m = chanZ cb m := if_pos hm

theorem chanZ_length (cb : CellB) (m : ℕ) : (chanZ cb m).length = cb.nC := by
  simp [chanZ, CellB.nC]

theorem chanZc_length (cb : CellB) (m : ℕ) : (chanZc cb m).length = cb.nC := by
  unfold chanZc
  split_ifs
  · exact chanZ_length cb m
  · exact List.length_replicate

theorem chanZ_getD_ctl (cb : CellB) (m i : ℕ) (hi : i < cb.N + 1) :
    (chanZ cb m).getD i 0 = ∑ k ∈ Finset.range (cb.N + 1),
      sv (smDec (slot cb.wc (cb.cm m) k)) * sv (bernI cb.N cb.D i k) := by
  unfold chanZ
  rw [getD_of_lt _ _ (by simp; omega), List.getElem_append_left (by simpa using hi)]
  simp

/-! ## Small facts -/

theorem abs_sv (x : Bool × ℕ) : |sv x| = (x.2 : ℤ) := by
  unfold sv; cases x.1 <;> simp

theorem sv_of_snd_zero (x : Bool × ℕ) (h : x.2 = 0) : sv x = 0 := by
  unfold sv; rw [h]; simp

theorem chan_land_cast (X K : ℕ) : ((Nat.land X (mask K) : ℕ) : ℤ) = (X : ℤ) % 2 ^ K := by
  rw [mask_eq]; exact toZ_mod_mask

theorem chan_land_lt (X K : ℕ) : Nat.land X (mask K) < 2 ^ K := by
  show X &&& mask K < 2 ^ K
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos K)

theorem modEq_sum_range {n : ℤ} (f g : ℕ → ℤ) : ∀ N, (∀ k < N, Int.ModEq n (f k) (g k)) →
    Int.ModEq n (∑ k ∈ Finset.range N, f k) (∑ k ∈ Finset.range N, g k)
  | 0, _ => by simp only [Finset.sum_range_zero]; exact Int.ModEq.refl 0
  | N + 1, h => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (modEq_sum_range f g N (fun k hk => h k (by omega))).add (h N (by omega))

/-- `2 |Σ zᵢ 2^(W i)| < 2^(W n)` when every `2 |zᵢ| < 2^W` -/
theorem two_abs_horner_lt (W : ℕ) : ∀ (z : List ℤ), (∀ x ∈ z, 2 * |x| < 2 ^ W) →
    2 * |horner (2 ^ W : ℤ) z| < 2 ^ (W * z.length)
  | [], _ => by simp
  | x :: z, h => by
    have ih := two_abs_horner_lt W z (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    have hW : (0 : ℤ) < 2 ^ W := by positivity
    rw [horner_cons, List.length_cons, mul_add, mul_one, pow_add]
    have h1 : 2 * |x| ≤ 2 ^ W - 1 := Int.le_sub_one_of_lt hx
    have h2 : 2 * |horner (2 ^ W : ℤ) z| ≤ 2 ^ (W * z.length) - 1 := Int.le_sub_one_of_lt ih
    have h3 : |x + 2 ^ W * horner (2 ^ W : ℤ) z| ≤ |x| + 2 ^ W * |horner (2 ^ W : ℤ) z| := by
      have := abs_add_le x (2 ^ W * horner (2 ^ W : ℤ) z)
      rwa [abs_mul, abs_of_pos hW] at this
    have h4 : 2 ^ W * (2 * |horner (2 ^ W : ℤ) z|) ≤ 2 ^ W * (2 ^ (W * z.length) - 1) :=
      mul_le_mul_of_nonneg_left h2 hW.le
    nlinarith

/-! ## Packed columns of `β̃` -/

theorem chan_packD_eq (W : ℕ) : ∀ L : List ℕ, packD W L = Nat.ofDigits (2 ^ W) L
  | [] => rfl
  | d :: L => by
    show d + packD W L <<< W = _
    rw [Nat.shiftLeft_eq, chan_packD_eq W L, Nat.ofDigits_cons, mul_comm]

theorem chan_packD_cons (W d : ℕ) (L : List ℕ) : packD W (d :: L) = d + packD W L * 2 ^ W := by
  show d + packD W L <<< W = _
  rw [Nat.shiftLeft_eq]

/-- the two's complement parts of a packed signed vector -/
theorem packD_sub_horner (W : ℕ) : ∀ ents : List (Bool × ℕ),
    ((packD W (ents.map fun b => cond b.1 0 b.2) : ℕ) : ℤ) -
        ((packD W (ents.map fun b => cond b.1 b.2 0) : ℕ) : ℤ) = horner (2 ^ W : ℤ) (ents.map sv)
  | [] => by simp
  | b :: ents => by
    have ih := packD_sub_horner W ents
    simp only [List.map_cons, chan_packD_cons, horner_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [← ih]
    rcases b with ⟨s, n⟩
    cases s <;> simp [sv] <;> ring

theorem bcol_final_mod (P Q KC : ℕ) (hQ : Q ≤ 2 ^ KC) :
    ((Nat.land (Nat.add P (Nat.sub (Nat.pow 2 KC) Q)) (mask KC) : ℕ) : ℤ) % 2 ^ KC = ((P : ℤ) - Q) % 2 ^ KC := by
  rw [chan_land_cast, Int.emod_emod]
  show ((P + (2 ^ KC - Q) : ℕ) : ℤ) % 2 ^ KC = _
  rw [Nat.cast_add, Nat.cast_sub hQ, Nat.cast_pow, Nat.cast_ofNat,
    show (P : ℤ) + (2 ^ KC - Q) = (P - Q) + 2 ^ KC by ring, ← Int.emod_eq_add_self_emod]

/-- column `k` of `β̃` is the packed vector `Σ_i β̃_ik 2^(WC i)` mod `2^KC` (entries `< 2^WC`) -/
theorem bcol_mod (N D WC KC k : ℕ) (hWC : 0 < WC) (hMK : WC * (N + 1) ≤ KC)
    (hb : ∀ i < N + 1, (bernI N D i k).2 < 2 ^ WC) :
    Int.ModEq (2 ^ KC) (bcol N D WC KC k : ℤ)
      (∑ i ∈ Finset.range (N + 1), sv (bernI N D i k) * 2 ^ (WC * i)) := by
  have hQ : packD WC (((List.range (Nat.succ N)).map fun i => bernI N D i k).map fun b => cond b.1 b.2 0) ≤
      2 ^ KC := by
    rw [chan_packD_eq]
    refine le_trans (ofDigits_lt_pow hWC _ ?_).le ?_
    · intro d hd
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hd
      obtain ⟨i, hi, rfl⟩ := hd
      have h1 := hb i hi
      generalize bernI N D i k = b at h1 ⊢
      rcases b with ⟨s, n⟩
      cases s
      · simp only [cond_false]; positivity
      · simpa using h1
    · simp only [List.length_map, List.length_range]
      exact Nat.pow_le_pow_right (by norm_num) hMK
  unfold Int.ModEq bcol
  dsimp only
  rw [bcol_final_mod _ _ _ hQ, packD_sub_horner, List.map_map, horner_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [pow_mul]

/-! ## The control part -/

theorem ctl_fold_spec : ∀ (L : List ((Bool × ℕ) × ℕ)) (pq : ℕ × ℕ),
    ((L.foldl (fun (pq : Nat × Nat) x => cond x.1.1 (pq.1, Nat.add pq.2 (Nat.mul x.1.2 x.2))
        (Nat.add pq.1 (Nat.mul x.1.2 x.2), pq.2)) pq).1 : ℤ) -
      ((L.foldl (fun (pq : Nat × Nat) x => cond x.1.1 (pq.1, Nat.add pq.2 (Nat.mul x.1.2 x.2))
        (Nat.add pq.1 (Nat.mul x.1.2 x.2), pq.2)) pq).2 : ℤ) =
      (pq.1 : ℤ) - pq.2 + (L.map fun x => sv x.1 * (x.2 : ℤ)).sum
  | [], pq => by simp
  | x :: L, pq => by
    rw [List.foldl_cons, ctl_fold_spec L, List.map_cons, List.sum_cons]
    rcases x with ⟨⟨s, n⟩, b⟩
    cases s <;> simp [sv] <;> ring

theorem ctl_final_mod (a b M : ℕ) :
    ((Nat.land (Nat.add a (Nat.sub (Nat.pow 2 M) (Nat.land b (mask M)))) (mask M) : ℕ) : ℤ) % 2 ^ M =
      ((a : ℤ) - b) % 2 ^ M := by
  have hle : Nat.land b (mask M) ≤ 2 ^ M := (chan_land_lt _ _).le
  rw [chan_land_cast, Int.emod_emod]
  show ((a + (2 ^ M - Nat.land b (mask M)) : ℕ) : ℤ) % 2 ^ M = _
  rw [Nat.cast_add, Nat.cast_sub hle, chan_land_cast, Nat.cast_pow, Nat.cast_ofNat]
  exact mod_helper _ _ _

/-- the stored control part is `Σ_i z_i 2^(WC i)` mod `2^M` (`z_i = Σ_k C_k β̃_ik`), provided the columns with a
nonzero centre coefficient have entries `< 2^WC` -/
theorem chanCtl_mod (N D WC KC wc cm : ℕ) (hWC : 0 < WC) (hMK : WC * (N + 1) ≤ KC)
    (hb : ∀ k < N + 1, (smDec (slot wc cm k)).2 ≠ 0 → ∀ i < N + 1, (bernI N D i k).2 < 2 ^ WC) :
    Int.ModEq (2 ^ (WC * (N + 1)))
      (chanCtl N (WC * (N + 1)) wc ((List.range (N + 1)).map (bcol N D WC KC)) cm : ℤ)
      (∑ i ∈ Finset.range (N + 1), (∑ k ∈ Finset.range (N + 1),
        sv (smDec (slot wc cm k)) * sv (bernI N D i k)) * 2 ^ (WC * i)) := by
  have hterm : ∀ k < N + 1, Int.ModEq (2 ^ (WC * (N + 1)))
      (sv (smDec (slot wc cm k)) * (bcol N D WC KC k : ℤ))
      (sv (smDec (slot wc cm k)) * ∑ i ∈ Finset.range (N + 1), sv (bernI N D i k) * 2 ^ (WC * i)) := by
    intro k hk
    by_cases h0 : (smDec (slot wc cm k)).2 = 0
    · rw [sv_of_snd_zero _ h0, zero_mul, zero_mul]
    · exact ((bcol_mod N D WC KC k hWC hMK (hb k hk h0)).of_dvd (pow_dvd_pow 2 hMK)).mul_left _
  have hsum := modEq_sum_range _ _ (N + 1) hterm
  have hR : ∑ k ∈ Finset.range (N + 1), sv (smDec (slot wc cm k)) *
      ∑ i ∈ Finset.range (N + 1), sv (bernI N D i k) * 2 ^ (WC * i) =
      ∑ i ∈ Finset.range (N + 1), (∑ k ∈ Finset.range (N + 1),
        sv (smDec (slot wc cm k)) * sv (bernI N D i k)) * 2 ^ (WC * i) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; ring
  rw [hR] at hsum
  refine Int.ModEq.trans ?_ hsum
  unfold chanCtl Int.ModEq
  dsimp only
  simp only [Nat.succ_eq_add_one]
  rw [ctl_final_mod, ctl_fold_spec, zip_range_map, List.map_map, list_sum_range]
  simp only [Function.comp_apply, Nat.cast_zero, sub_self, zero_add]

/-! ## Sign extension and direction -/

/-- sign extension of an `M`-bit two's complement numeral to `KC` bits (as in `chanAll`) -/
def sgnExt (KC M cv : ℕ) : ℕ :=
  cond (Nat.beq (Nat.land (Nat.shiftRight cv (Nat.sub M 1)) 1) 1) (Nat.add cv (Nat.sub (Nat.pow 2 KC) (Nat.pow 2 M)))
    cv

/-- `cx ± d` mod `2^KC` (as in `chanAll`) -/
def addDir (KC cx : ℕ) (s : Bool) (d : ℕ) : ℕ :=
  Nat.land (cond s (Nat.add cx (Nat.sub (Nat.pow 2 KC) d)) (Nat.add cx d)) (mask KC)

/-- one channel vector of `chanAll` -/
def chanOne (KC M WC N1 : ℕ) (dirT : ℕ → ℕ) (dirQ : ℕ → Bool × ℕ) (cv m : ℕ) : ℕ :=
  addDir KC (sgnExt KC M cv) (dirQ m).1 (Nat.shiftLeft (dirQ m).2 (Nat.mul WC (Nat.add N1 (dirT m))))

theorem sgnExt_mod (KC M cv : ℕ) (Z : ℤ) (hM : 1 ≤ M) (hMK : M ≤ KC) (hcv : cv < 2 ^ M)
    (hZ : Int.ModEq (2 ^ M) (cv : ℤ) Z) (hZb : 2 * |Z| < 2 ^ M) :
    Int.ModEq (2 ^ KC) (sgnExt KC M cv : ℤ) Z := by
  have hpow : (2 : ℕ) ^ M = 2 * 2 ^ (M - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpowZ : (2 : ℤ) ^ M = 2 * 2 ^ (M - 1) := by exact_mod_cast hpow
  have hp : (0 : ℤ) < 2 ^ (M - 1) := by positivity
  have hMKle : 2 ^ M ≤ 2 ^ KC := Nat.pow_le_pow_right (by norm_num) hMK
  have hlt2 : cv / 2 ^ (M - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc cv < 2 ^ M := hcv
      _ = 2 * 2 ^ (M - 1) := hpow
  have hbit : Nat.land (Nat.shiftRight cv (Nat.sub M 1)) 1 = cv / 2 ^ (M - 1) := by
    show (cv >>> (M - 1)) &&& (2 ^ 1 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, pow_one, Nat.mod_eq_of_lt hlt2]
  have hcvZ : (cv : ℤ) = Z % 2 ^ M := by
    have h1 : (cv : ℤ) % 2 ^ M = cv := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hcv)
    rw [← h1]; exact hZ
  unfold sgnExt
  rw [hbit]
  by_cases hZ0 : 0 ≤ Z
  · have hZlt : Z < 2 ^ (M - 1) := by
      rw [abs_of_nonneg hZ0] at hZb; linarith
    have hcvZ' : (cv : ℤ) = Z := by rw [hcvZ, Int.emod_eq_of_lt hZ0 (by linarith)]
    have hdiv : cv / 2 ^ (M - 1) = 0 := by
      apply Nat.div_eq_of_lt
      have : (cv : ℤ) < 2 ^ (M - 1) := by rw [hcvZ']; exact hZlt
      exact_mod_cast this
    rw [hdiv]
    show Int.ModEq _ (cv : ℤ) Z
    rw [hcvZ']
  · push Not at hZ0
    have hZgt : -2 ^ (M - 1) < Z := by
      rw [abs_of_neg hZ0] at hZb; linarith
    have hcvZ' : (cv : ℤ) = Z + 2 ^ M := by
      rw [hcvZ, Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by linarith) (by linarith)]
    have hdiv : cv / 2 ^ (M - 1) = 1 := by
      have h1 : 2 ^ (M - 1) ≤ cv := by
        have : (2 : ℤ) ^ (M - 1) ≤ cv := by rw [hcvZ']; linarith
        exact_mod_cast this
      have h2 := Nat.div_pos h1 (Nat.two_pow_pos _)
      omega
    rw [hdiv]
    show Int.ModEq _ ((cv + (2 ^ KC - 2 ^ M) : ℕ) : ℤ) Z
    rw [Nat.cast_add, Nat.cast_sub hMKle, hcvZ']
    push_cast
    unfold Int.ModEq
    rw [show Z + 2 ^ M + (2 ^ KC - 2 ^ M) = Z + 2 ^ KC by ring, ← Int.emod_eq_add_self_emod]

theorem addDir_mod (KC cx e : ℕ) (dq : Bool × ℕ) (hd : dq.2 * 2 ^ e ≤ 2 ^ KC) :
    Int.ModEq (2 ^ KC) (addDir KC cx dq.1 (Nat.shiftLeft dq.2 e) : ℤ) ((cx : ℤ) + sv dq * 2 ^ e) := by
  have hsh : Nat.shiftLeft dq.2 e = dq.2 * 2 ^ e := Nat.shiftLeft_eq _ _
  unfold addDir Int.ModEq
  rw [chan_land_cast, Int.emod_emod, hsh]
  rcases dq with ⟨s, q⟩
  have hd' : q * 2 ^ e ≤ 2 ^ KC := hd
  cases s
  · show ((cx + q * 2 ^ e : ℕ) : ℤ) % 2 ^ KC = ((cx : ℤ) + sv (false, q) * 2 ^ e) % 2 ^ KC
    simp [sv]
  · show ((cx + (2 ^ KC - q * 2 ^ e) : ℕ) : ℤ) % 2 ^ KC = ((cx : ℤ) + sv (true, q) * 2 ^ e) % 2 ^ KC
    rw [Nat.cast_add, Nat.cast_sub hd']
    push_cast
    rw [show (cx : ℤ) + (2 ^ KC - (q : ℤ) * 2 ^ e) = ((cx : ℤ) + sv (true, q) * 2 ^ e) + 2 ^ KC by
      simp [sv]; ring, ← Int.emod_eq_add_self_emod]

theorem chanAll_length (KC M WC N1 : ℕ) (dirT : ℕ → ℕ) (dirQ : ℕ → Bool × ℕ) :
    ∀ (cvs : List ℕ) (m0 : ℕ), (chanAll KC M WC N1 dirT dirQ cvs m0).length = cvs.length
  | [], _ => rfl
  | cv :: cvs, m0 => by
    show (_ :: chanAll KC M WC N1 dirT dirQ cvs (Nat.succ m0)).length = _
    rw [List.length_cons, chanAll_length KC M WC N1 dirT dirQ cvs, List.length_cons]

theorem chanAll_getD (KC M WC N1 : ℕ) (dirT : ℕ → ℕ) (dirQ : ℕ → Bool × ℕ) :
    ∀ (cvs : List ℕ) (m0 m : ℕ), m < cvs.length →
      (chanAll KC M WC N1 dirT dirQ cvs m0).getD m 0 = chanOne KC M WC N1 dirT dirQ (cvs.getD m 0) (m0 + m)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | cv :: cvs, m0, 0, _ => rfl
  | cv :: cvs, m0, m + 1, h => by
    show (chanAll KC M WC N1 dirT dirQ cvs (Nat.succ m0)).getD m 0 = _
    rw [chanAll_getD KC M WC N1 dirT dirQ cvs (Nat.succ m0) m (by simp at h; omega), List.getD_cons_succ]
    congr 1
    omega

/-! ## The integer channel vector -/

theorem horner_appendZ (t : ℤ) : ∀ (a b : List ℤ), horner t (a ++ b) = horner t a + t ^ a.length * horner t b
  | [], b => by simp
  | x :: a, b => by
    rw [List.cons_append, horner_cons, horner_cons, horner_appendZ t a b, List.length_cons, pow_succ]
    ring

theorem chanZ_horner (cb : CellB) (m : ℕ) (ht : cb.dirT m < cb.nT) :
    horner (2 ^ cb.WC : ℤ) (chanZ cb m) =
      ∑ i ∈ Finset.range (cb.N + 1), (∑ k ∈ Finset.range (cb.N + 1),
          sv (smDec (slot cb.wc (cb.cm m) k)) * sv (bernI cb.N cb.D i k)) * 2 ^ (cb.WC * i) +
        sv (cb.dirQ m) * 2 ^ (cb.WC * (cb.N + 1 + cb.dirT m)) := by
  unfold chanZ
  rw [horner_appendZ, horner_range, horner_range, List.length_map, List.length_range]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; rw [← pow_mul]
  · rw [Finset.sum_eq_single (cb.dirT m)]
    · rw [if_pos rfl, ← pow_mul, ← pow_mul,
        show cb.WC * (cb.N + 1 + cb.dirT m) = cb.WC * (cb.N + 1) + cb.WC * cb.dirT m by ring, pow_add]
      ring
    · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr ht) h

theorem bernI_le_bmax (N D i k : ℕ) (hi : i < N + 1) : (bernI N D i k).2 ≤ bmax N D k := by
  unfold bmax
  exact (foldl_max_ge (fun i => (bernI N D i k).2) (List.range (Nat.succ N)) 0).2 i (List.mem_range.mpr hi)

theorem chanBnd_spec (N wc cmax D cm : ℕ) (dq : Bool × ℕ)
    (h : chanBnd N wc cmax ((List.range (Nat.succ N)).map (bmax N D)) cm dq = true) :
    ∑ k ∈ Finset.range (N + 1), (smDec (slot wc cm k)).2 * bmax N D k ≤ cmax ∧ dq.2 ≤ cmax := by
  unfold chanBnd at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  rw [zip_range_map, List.map_map, lsum_eq_sum, list_sum_range'] at h1
  simpa using h1

/-- the control channel values are bounded by `cmax` -/
theorem ctl_abs_le (N D wc cm cmax : ℕ)
    (hB : ∑ k ∈ Finset.range (N + 1), (smDec (slot wc cm k)).2 * bmax N D k ≤ cmax) (i : ℕ) (hi : i < N + 1) :
    |∑ k ∈ Finset.range (N + 1), sv (smDec (slot wc cm k)) * sv (bernI N D i k)| ≤ (cmax : ℤ) := by
  calc |∑ k ∈ Finset.range (N + 1), sv (smDec (slot wc cm k)) * sv (bernI N D i k)|
      ≤ ∑ k ∈ Finset.range (N + 1), |sv (smDec (slot wc cm k)) * sv (bernI N D i k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), (((smDec (slot wc cm k)).2 * bmax N D k : ℕ) : ℤ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_sv, abs_sv, Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast bernI_le_bmax N D i k hi) (by positivity)
    _ = ((∑ k ∈ Finset.range (N + 1), (smDec (slot wc cm k)).2 * bmax N D k : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ cmax := by exact_mod_cast hB

/-! ## The channel leaf -/

/-- **Channel leaf soundness.** The channel vectors `chanAll … cvc 0` are the packed integer vectors `chanZc cb m`
(`= chanZ cb m` for `m < nin`, `chanZc_of_lt`), all values bounded by `cmax`. -/
theorem chanOk_sound (cb : CellB) (nin : ℕ) (h : chanOk cb nin = true) :
    ChanSem nin cb (chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0) (chanZc cb) := by
  have h' := h
  unfold chanOk at h'
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, List.all_eq_true, List.mem_range] at h'
  obtain ⟨⟨hlen, hctl⟩, hbnd, h2c, -⟩ := h'
  have h2c' : 2 * cb.cmax < 2 ^ cb.WC := h2c
  have hcl : (chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0).length = cb.cvc.length :=
    chanAll_length _ _ _ _ _ _ _ _
  refine ⟨chanZc_length cb, fun m x hx => ?_, fun m hm => ?_, (hcl.trans hlen).ge⟩
  · -- the bound
    unfold chanZc at hx
    split_ifs at hx with hm
    · obtain ⟨hB, -⟩ := hbnd m (hlen ▸ hm)
      obtain ⟨hB1, hB2⟩ := chanBnd_spec cb.N cb.wc cb.cmax cb.D (cb.cm m) (cb.dirQ m) hB
      unfold chanZ at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact ctl_abs_le cb.N cb.D cb.wc (cb.cm m) cb.cmax hB1 i (List.mem_range.mp hi)
      · obtain ⟨tt, _, rfl⟩ := List.mem_map.mp hx
        split_ifs
        · rw [abs_sv]; exact_mod_cast hB2
        · simp
    · rw [List.eq_of_mem_replicate hx]; simp
  · -- the congruence
    rw [hcl] at hm
    obtain ⟨hB, ht⟩ := hbnd m (hlen ▸ hm)
    obtain ⟨hB1, hB2⟩ := chanBnd_spec cb.N cb.wc cb.cmax cb.D (cb.cm m) (cb.dirQ m) hB
    show Int.ModEq (2 ^ cb.KC) _ _
    rw [chanZc_of_lt cb hm]
    rcases Nat.eq_zero_or_pos cb.WC with hW0 | hW
    · have hK0 : cb.KC = 0 := by show cb.WC * cb.nC = 0; rw [hW0, zero_mul]
      rw [hK0, pow_zero]
      exact Int.modEq_one
    have hKC : cb.KC = cb.WC * (cb.N + 1 + cb.nT) := rfl
    have hMK : cb.WC * (cb.N + 1) ≤ cb.KC := by rw [hKC]; exact Nat.mul_le_mul_left _ (by omega)
    have hcm : cb.cmax < 2 ^ cb.WC := by omega
    -- the stored control part
    have hcv : cb.cvc.getD m 0 = chanCtl cb.N cb.M cb.wc cb.bcols (cb.cm m) := by
      have hzl : m < (cb.cvc.zip (List.range nin)).length := by simp [List.length_zip]; omega
      have hmem := List.getElem_mem hzl
      rw [List.getElem_zip] at hmem
      simp only [List.getElem_range] at hmem
      rw [getD_of_lt _ _ hm]
      exact hctl _ hmem
    have hbb : ∀ k < cb.N + 1, (smDec (slot cb.wc (cb.cm m) k)).2 ≠ 0 →
        ∀ i < cb.N + 1, (bernI cb.N cb.D i k).2 < 2 ^ cb.WC := by
      intro k hk hne i hi
      have h1 := bernI_le_bmax cb.N cb.D i k hi
      have h2 : bmax cb.N cb.D k ≤ cb.cmax := by
        calc bmax cb.N cb.D k ≤ (smDec (slot cb.wc (cb.cm m) k)).2 * bmax cb.N cb.D k :=
              Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
          _ ≤ ∑ k ∈ Finset.range (cb.N + 1), (smDec (slot cb.wc (cb.cm m) k)).2 * bmax cb.N cb.D k :=
              Finset.single_le_sum (f := fun k => (smDec (slot cb.wc (cb.cm m) k)).2 * bmax cb.N cb.D k)
                (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
          _ ≤ cb.cmax := hB1
      omega
    have hctlmod := chanCtl_mod cb.N cb.D cb.WC cb.KC cb.wc (cb.cm m) hW hMK hbb
    -- the control value `Z` and its bound
    have hZb : 2 * |∑ i ∈ Finset.range (cb.N + 1), (∑ k ∈ Finset.range (cb.N + 1),
        sv (smDec (slot cb.wc (cb.cm m) k)) * sv (bernI cb.N cb.D i k)) * 2 ^ (cb.WC * i)| <
        2 ^ (cb.WC * (cb.N + 1)) := by
      have hh := two_abs_horner_lt cb.WC ((List.range (cb.N + 1)).map fun i => ∑ k ∈ Finset.range (cb.N + 1),
          sv (smDec (slot cb.wc (cb.cm m) k)) * sv (bernI cb.N cb.D i k)) (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have h1 := ctl_abs_le cb.N cb.D cb.wc (cb.cm m) cb.cmax hB1 i (List.mem_range.mp hi)
        have h2 : (2 * cb.cmax : ℤ) < 2 ^ cb.WC := by exact_mod_cast h2c'
        linarith)
      rw [List.length_map, List.length_range, horner_range] at hh
      simpa only [← pow_mul] using hh
    have hcvlt : cb.cvc.getD m 0 < 2 ^ (cb.WC * (cb.N + 1)) := by rw [hcv]; exact chan_land_lt _ _
    have hsx := sgnExt_mod cb.KC (cb.WC * (cb.N + 1)) (cb.cvc.getD m 0) _
      (Nat.mul_pos hW (Nat.succ_pos _)) hMK hcvlt (by rw [hcv]; exact hctlmod) hZb
    -- the direction
    have hd : (cb.dirQ m).2 * 2 ^ (cb.WC * (cb.N + 1 + cb.dirT m)) ≤ 2 ^ cb.KC := by
      calc (cb.dirQ m).2 * 2 ^ (cb.WC * (cb.N + 1 + cb.dirT m))
          ≤ 2 ^ cb.WC * 2 ^ (cb.WC * (cb.N + 1 + cb.dirT m)) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ (cb.WC * (cb.N + 1 + cb.dirT m + 1)) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ cb.KC := Nat.pow_le_pow_right (by norm_num) (by rw [hKC]; exact Nat.mul_le_mul_left _ (by omega))
    have hdir := addDir_mod cb.KC (sgnExt cb.KC (cb.WC * (cb.N + 1)) (cb.cvc.getD m 0))
      (cb.WC * (cb.N + 1 + cb.dirT m)) (cb.dirQ m) hd
    rw [chanAll_getD _ _ _ _ _ _ cb.cvc 0 m hm, zero_add, chanZ_horner cb m ht]
    exact hdir.trans (Int.ModEq.add_right _ hsx)

/-- the scalar facts of the channel leaf used by the row theorem -/
theorem chanOk_facts (cb : CellB) (nin : ℕ) (h : chanOk cb nin = true) :
    cb.U.ok = true ∧ cb.ucN < 2 ^ (2 * cb.BT + 2) ∧ cb.rN < 2 ^ (2 * cb.BT + 2) ∧
    2 * (cb.ucN + cb.rN) ≤ 2 ^ 256 ∧ 1 ≤ cb.Kt ∧ 2 * cb.cmax < 2 ^ cb.WC := by
  unfold chanOk at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨-, -, h2c, hU, hu0, hu1, hu2, hKt⟩ := h
  exact ⟨hU, hu0, hu1, hu2, hKt, h2c⟩

theorem chanOk_len (cb : CellB) (nin : ℕ) (h : chanOk cb nin = true) : cb.cvc.length = nin := by
  unfold chanOk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1

/-- on the checked coordinates the channel vectors of `chanOk_sound` are `chanZ` -/
theorem chanZc_eq (cb : CellB) (nin : ℕ) (h : chanOk cb nin = true) {m : ℕ} (hm : m < nin) :
    chanZc cb m = chanZ cb m :=
  chanZc_of_lt cb (by rw [chanOk_len cb nin h]; exact hm)

/-! ## Arithmetic of `β̃` -/

theorem fact_eq_factorial : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by
    show Nat.mul (n + 1) (fact n) = _
    rw [fact_eq_factorial n, Nat.factorial_succ]
    rfl

theorem chooseF_eq (n k : ℕ) : chooseF n k = n.choose k := by
  unfold chooseF
  by_cases hk : k ≤ n
  · rw [Nat.ble_eq_true_of_le hk]
    show fact n / (fact k * fact (n - k)) = _
    rw [fact_eq_factorial, fact_eq_factorial, fact_eq_factorial, Nat.choose_eq_factorial_div_factorial hk]
  · have h1 : Nat.ble k n = false := by
      rw [Bool.eq_false_iff]; intro h; exact hk (Nat.le_of_ble_eq_true h)
    rw [h1, Nat.choose_eq_zero_of_lt (by omega)]
    rfl

theorem foldl_lcm_spec (f : ℕ → ℕ) : ∀ (l : List ℕ) (D0 : ℕ),
    D0 ∣ l.foldl (fun D k => Nat.lcm D (f k)) D0 ∧ ∀ k ∈ l, f k ∣ l.foldl (fun D k => Nat.lcm D (f k)) D0
  | [], D0 => ⟨dvd_rfl, by simp⟩
  | x :: l, D0 => by
    obtain ⟨h1, h2⟩ := foldl_lcm_spec f l (Nat.lcm D0 (f x))
    refine ⟨dvd_trans (Nat.dvd_lcm_left _ _) h1, fun k hk => ?_⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · exact dvd_trans (Nat.dvd_lcm_right _ _) h1
    · exact h2 k hk

theorem foldl_lcm_pos (f : ℕ → ℕ) : ∀ (l : List ℕ) (D0 : ℕ), 0 < D0 → (∀ k ∈ l, 0 < f k) →
    0 < l.foldl (fun D k => Nat.lcm D (f k)) D0
  | [], _, h0, _ => h0
  | x :: l, D0, h0, hf => foldl_lcm_pos f l _ (Nat.lcm_pos h0 (hf x (by simp)))
      (fun k hk => hf k (List.mem_cons_of_mem _ hk))

/-- `C(N,k) ∣ D_N` -/
theorem chooseF_dvd_bernDen (N k : ℕ) (hk : k ≤ N) : chooseF N k ∣ bernDen N :=
  (foldl_lcm_spec (chooseF N) (List.range (Nat.succ N)) 1).2 k (List.mem_range.mpr (by omega))

theorem bernDen_pos (N : ℕ) : 0 < bernDen N :=
  foldl_lcm_pos (chooseF N) (List.range (Nat.succ N)) 1 Nat.one_pos (fun k hk => by
    rw [chooseF_eq]; exact Nat.choose_pos (by have := List.mem_range.mp hk; omega))

theorem sv_diff (a b q : ℕ) :
    sv (Nat.blt a b, Nat.mul (Nat.add (Nat.sub a b) (Nat.sub b a)) q) = ((a : ℤ) - b) * q := by
  simp only [sv, Nat.blt_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  split_ifs with h
  · rw [Nat.sub_eq_zero_of_le h.le, zero_add, Nat.cast_mul, Nat.cast_sub h.le]; ring
  · push Not at h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_mul, Nat.cast_sub h]

theorem cond_parity (n y : ℕ) :
    ((cond (Nat.beq (Nat.mod n 2) 0) y 0 : ℕ) : ℤ) - ((cond (Nat.beq (Nat.mod n 2) 1) y 0 : ℕ) : ℤ) =
      (-1) ^ n * (y : ℤ) := by
  rcases Nat.even_or_odd n with h | h
  · have h0 : Nat.mod n 2 = 0 := Nat.even_iff.mp h
    rw [h0, h.neg_one_pow]
    show ((y : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 1 * (y : ℤ)
    simp
  · have h1 : Nat.mod n 2 = 1 := Nat.odd_iff.mp h
    rw [h1, h.neg_one_pow]
    show ((0 : ℕ) : ℤ) - ((y : ℕ) : ℤ) = -1 * (y : ℤ)
    simp

/-- `β̃_ik = (Σ_j (-1)^(k-j) C(i,j) C(N-i,k-j)) · (D / C(N,k))` -/
theorem sv_bernI (N D i k : ℕ) :
    sv (bernI N D i k) = (∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (k - j) * (i.choose j : ℤ) * ((N - i).choose (k - j) : ℤ)) * ((D / N.choose k : ℕ) : ℤ) := by
  unfold bernI
  dsimp only
  rw [sv_diff, lsum_eq_sum, lsum_eq_sum, list_sum_range', list_sum_range', Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib, chooseF_eq N k]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [cond_parity, chooseF_eq, chooseF_eq]
  simp only [Nat.mul_eq, Nat.sub_eq, Nat.cast_mul]
  ring

end ThomsonCompact.Floor.B
