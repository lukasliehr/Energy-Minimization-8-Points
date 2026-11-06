import ThomsonCompact.Packed.Comp
import ThomsonCompact.Packed.Bridge
import AllS.Units.N_AI.N_scalar_models.ProductGateSupport

/-!
# Bridges between old `ℚ`-box Taylor models and packed TMs

* **reverse**: `ofBoxes c L err` packs coefficient boxes `L = [(loₖ, hiₖ)]` and an error `err` (old
  `Blueprint.CAP.TM` / `QModel` data, `boxList`), rounding outward to the grid `2^-S` in the kernel
  (`cₖ = ⌊loₖ 2^S⌋`, error `⌈err 2^S⌉ + Σ (⌈hiₖ 2^S⌉ - cₖ)`); `ofBoxes_sound : M.Valid f → ok → Encl`.
* **forward**: `toQModel c T : QModel c.N` (point intervals) with `Encl.validQ : Encl → (toQModel c T).asTM.Valid`.
-/

namespace ThomsonCompact.Packed
open Blueprint.CAP

variable {N S B W : ℕ}

/-- the coefficient boxes of an old TM -/
def boxList {n : ℕ} (M : Blueprint.CAP.TM n) : List (ℚ × ℚ) :=
  List.ofFn (fun k => ((M.coeff k).lo, (M.coeff k).hi))

/-- an old TM (e.g. `QModel.asTM` of a per-cell height model) as a packed TM -/
def ofOldTM (c : Ctx) {n : ℕ} (M : Blueprint.CAP.TM n) : TM := ofBoxes c (boxList M) M.error

/-! ## Rounding facts -/

theorem qFloor_le (S : ℕ) (q : ℚ) : ((qFloor (2 ^ S) q : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ S := by
  unfold qFloor
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have h1 := Int.ediv_mul_le (q.num * ((2 ^ S : ℕ) : ℤ)) hd
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  rw [Rat.cast_def, div_mul_eq_mul_div, le_div_iff₀ hdR]
  have h2 : (((q.num * ((2 ^ S : ℕ) : ℤ) / (q.den : ℤ)) * (q.den : ℤ) : ℤ) : ℝ) ≤
      ((q.num * ((2 ^ S : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2 ⊢
  linarith

theorem le_qCeil (S : ℕ) (q : ℚ) : (q : ℝ) * 2 ^ S ≤ ((qCeil (2 ^ S) q : ℤ) : ℝ) := by
  unfold qCeil
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have h1 := Int.ediv_mul_le (-(q.num * ((2 ^ S : ℕ) : ℤ))) hd
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  rw [Rat.cast_def, div_mul_eq_mul_div, div_le_iff₀ hdR]
  have h2 : (((-(q.num * ((2 ^ S : ℕ) : ℤ)) / (q.den : ℤ)) * (q.den : ℤ) : ℤ) : ℝ) ≤
      ((-(q.num * ((2 ^ S : ℕ) : ℤ)) : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2 ⊢
  linarith

/-! ## Packing -/

theorem packD_eq (W : ℕ) : ∀ L : List ℕ, packD W L = Nat.ofDigits (2 ^ W) L
  | [] => rfl
  | d :: L => by
    show d + packD W L <<< W = _
    rw [Nat.shiftLeft_eq, packD_eq W L, Nat.ofDigits_cons, mul_comm]

theorem allSmall_iff (twoB : ℕ) : ∀ L : List ℤ, allSmall twoB L = true → ∀ z ∈ L, z.natAbs < twoB
  | [], _ => by simp
  | z :: L, h => by
    have e : allSmall twoB (z :: L) = (Nat.blt z.natAbs twoB && allSmall twoB L) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact allSmall_iff twoB L h.2 x hx

theorem digitsN_ofDigits_pad {W : ℕ} (m : ℕ) (L : List ℕ) (hL : L.length ≤ m) (hd : ∀ d ∈ L, d < 2 ^ W) :
    digitsN W m (Nat.ofDigits (2 ^ W) L) = L ++ List.replicate (m - L.length) 0 := by
  have hW : 0 < 2 ^ W := Nat.two_pow_pos W
  have hd' : ∀ d ∈ L ++ List.replicate (m - L.length) 0, d < 2 ^ W := by
    intro d hdm
    rcases List.mem_append.mp hdm with h | h
    · exact hd d h
    · rw [List.eq_of_mem_replicate h]; exact hW
  have hlen : (L ++ List.replicate (m - L.length) 0).length = m := by simp; omega
  have hval : Nat.ofDigits (2 ^ W) (L ++ List.replicate (m - L.length) 0) = Nat.ofDigits (2 ^ W) L := by
    rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, mul_zero, add_zero]
  have := digitsN_ofDigits (W := W) _ hd'
  rw [hlen, hval] at this
  exact this

theorem zipWith_toNat (L : List ℤ) :
    List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) (L.map Int.toNat) (L.map (fun z => Int.toNat (-z))) = L := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, ih, Int.toNat_sub_toNat_neg]

theorem zipWith_zeros (k : ℕ) :
    List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) (List.replicate k 0) (List.replicate k 0) =
      List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.zipWith_cons_cons, ih]; simp

theorem horner_ofFn {R : Type*} [CommSemiring R] (t : R) :
    ∀ {m : ℕ} (g : Fin m → R), horner t (List.ofFn g) = ∑ k : Fin m, g k * t ^ (k : ℕ)
  | 0, g => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, horner, horner_ofFn t (fun i => g i.succ), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem boxErr_ofFn (twoS : ℕ) : ∀ {m : ℕ} (g : Fin m → ℚ × ℚ),
    boxErr twoS (List.ofFn g) = ∑ k : Fin m, Int.toNat (qCeil twoS (g k).2 - qFloor twoS (g k).1)
  | 0, g => by simp [boxErr]
  | m + 1, g => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    show Int.toNat (qCeil twoS (g 0).2 - qFloor twoS (g 0).1) + boxErr twoS (List.ofFn fun i => g i.succ) = _
    rw [boxErr_ofFn twoS (fun i => g i.succ)]

/-! ## Reverse bridge -/

/-- **reverse bridge**: an old TM-valid box model gives a packed enclosure (outward rounded in the kernel) -/
theorem ofBoxes_sound (hg : Good N S B W) {n : ℕ} (M : Blueprint.CAP.TM n) {f : ℝ → ℝ} (hM : M.Valid f)
    (hok : (ofOldTM (mkCtx N S B W) M).ok = true) :
    Encl (mkCtx N S B W) (ofOldTM (mkCtx N S B W) M) f := by
  obtain ⟨herr, a, ha, hf⟩ := hM
  set cl : List ℤ := (boxList M).map (fun b => qFloor (2 ^ S) b.1) with hcl
  set P := packD W (cl.map Int.toNat) with hP
  set Q := packD W (cl.map (fun z => Int.toNat (-z))) with hQ
  set eT := Nat.add (Int.toNat (qCeil (2 ^ S) M.error)) (boxErr (2 ^ S) (boxList M)) with heT
  have hokE : (ofOldTM (mkCtx N S B W) M).ok =
      ((ofPQ (mkCtx N S B W) P Q eT).ok && allSmall (2 ^ B) cl && Nat.ble (boxList M).length (N + 1)) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨hpq, hsmall⟩, hlen⟩ := hok
  have hsm := allSmall_iff _ cl hsmall
  have hlenL : (boxList M).length = n + 1 := by simp [boxList]
  have hclen : cl.length = n + 1 := by simp [hcl, hlenL]
  have hnN : n + 1 ≤ N + 1 := by rw [← hlenL]; exact hlen
  have hBW : 2 ^ B ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega)
  -- the decoded coefficient list
  have hdP : ∀ d ∈ cl.map Int.toNat, d < 2 ^ W := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    have := hsm z hz
    omega
  have hdQ : ∀ d ∈ cl.map (fun z => Int.toNat (-z)), d < 2 ^ W := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    have := hsm z hz
    omega
  have hpqc : pqCoeffs W (N + 1) P Q = cl ++ List.replicate (N + 1 - (n + 1)) 0 := by
    unfold pqCoeffs
    rw [hP, hQ, packD_eq, packD_eq, digitsN_ofDigits_pad (N + 1) _ (by simp [hclen]; omega) hdP,
      digitsN_ofDigits_pad (N + 1) _ (by simp [hclen]; omega) hdQ]
    simp only [List.length_map, hclen]
    rw [List.zipWith_append (by simp), zipWith_toNat, zipWith_zeros]
  -- polynomial of the packed TM
  have h0 := ofPQ_sound hg P Q 0 hpq
  have hpoly : ∀ t : ℝ, evalZ (pqCoeffs W (N + 1) P Q) t / 2 ^ S =
      ∑ k : Fin (n + 1), ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S * t ^ (k : ℕ) := by
    intro t
    rw [hpqc, evalZ, List.map_append, List.map_replicate, Int.cast_zero, horner_append_zeros]
    have : cl = List.ofFn (fun k : Fin (n + 1) => qFloor (2 ^ S) (M.coeff k).lo) := by
      simp only [hcl, boxList, List.map_ofFn, Function.comp_def]
    rw [this, List.map_ofFn, horner_ofFn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Function.comp]
    ring
  -- error accounting
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hrem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - evalZ (pqCoeffs W (N + 1) P Q) t / 2 ^ S| ≤
      (eT : ℝ) / 2 ^ (mkCtx N S B W).S := by
    intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    rw [hpoly t]
    have hft := hf t ht
    have hsplit : f t - ∑ k : Fin (n + 1), ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S * t ^ (k : ℕ) =
        (f t - scalarEval a t) +
          ∑ k : Fin (n + 1), (a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S) * t ^ (k : ℕ) := by
      simp only [scalarEval, sub_mul, Finset.sum_sub_distrib]
      ring
    have hcoef : ∀ k : Fin (n + 1), |(a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S) * t ^ (k : ℕ)| ≤
        (((Int.toNat (qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo) : ℕ) : ℝ)) / 2 ^ S := by
      intro k
      have hk := ha k
      have hlo := qFloor_le S (M.coeff k).lo
      have hhi := le_qCeil S (M.coeff k).hi
      have h1 : ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S ≤ a k := by
        rw [div_le_iff₀ h2S]; nlinarith [hk.1]
      have h2 : a k ≤ ((qCeil (2 ^ S) (M.coeff k).hi : ℤ) : ℝ) / 2 ^ S := by
        rw [le_div_iff₀ h2S]; nlinarith [hk.2]
      have h3 : ((qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) ≤
          (((Int.toNat (qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo) : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      have htk : |t ^ (k : ℕ)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hta
      rw [abs_mul]
      calc |a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S| * |t ^ (k : ℕ)|
          ≤ |a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S| * 1 :=
            mul_le_mul_of_nonneg_left htk (abs_nonneg _)
        _ = a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S := by
            rw [mul_one, abs_of_nonneg (by linarith)]
        _ ≤ ((qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S := by
            push_cast; rw [sub_div]; linarith
        _ ≤ _ := by
            apply div_le_div_of_nonneg_right _ h2S.le
            exact_mod_cast h3
    have hsum : |∑ k : Fin (n + 1), (a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S) * t ^ (k : ℕ)| ≤
        ∑ k : Fin (n + 1), (((Int.toNat (qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo) : ℕ) : ℝ)) / 2 ^ S :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hcoef k))
    have herr' : (M.error : ℝ) ≤ (((Int.toNat (qCeil (2 ^ S) M.error)) : ℕ) : ℝ) / 2 ^ S := by
      rw [le_div_iff₀ h2S]
      have := le_qCeil S M.error
      have h4 : ((qCeil (2 ^ S) M.error : ℤ) : ℝ) ≤ (((Int.toNat (qCeil (2 ^ S) M.error) : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      push_cast at h4
      linarith
    have hbe : boxErr (2 ^ S) (boxList M) =
        ∑ k : Fin (n + 1), Int.toNat (qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo) := by
      rw [boxList, boxErr_ofFn]
    have heTR : (eT : ℝ) / 2 ^ S = (((Int.toNat (qCeil (2 ^ S) M.error)) : ℕ) : ℝ) / 2 ^ S +
        ∑ k : Fin (n + 1), (((Int.toNat (qCeil (2 ^ S) (M.coeff k).hi - qFloor (2 ^ S) (M.coeff k).lo) : ℕ) : ℝ)) / 2 ^ S := by
      show ((Int.toNat (qCeil (2 ^ S) M.error) + boxErr (2 ^ S) (boxList M) : ℕ) : ℝ) / 2 ^ S = _
      rw [hbe]
      push_cast
      rw [add_div, Finset.sum_div]
    rw [hsplit]
    simp only [mk_S]
    rw [heTR]
    calc |(f t - scalarEval a t) + ∑ k : Fin (n + 1), (a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S) * t ^ (k : ℕ)|
        ≤ |f t - scalarEval a t| + |∑ k : Fin (n + 1), (a k - ((qFloor (2 ^ S) (M.coeff k).lo : ℤ) : ℝ) / 2 ^ S) * t ^ (k : ℕ)| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add (hft.trans herr') hsum
  have hw := widen_sound eT h0 hrem
  exact hw.of_fields rfl rfl rfl (by show eT = 0 + eT; rw [Nat.zero_add])

/-! ## Forward bridge to `QModel` -/

/-- the packed TM as an old `QModel` with point intervals -/
def toQModel (c : Ctx) (T : TM) : QModel c.N :=
  ⟨fun k => ⟨(((decode c T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ c.S, (((decode c T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ c.S⟩,
    (T.e : ℚ) / 2 ^ c.S⟩

theorem toQModel_asTM (c : Ctx) (T : TM) : (toQModel c T).asTM = toTM c T := rfl

/-- **forward bridge** to the `QModel` form consumed by the F0 interface -/
theorem Encl.validQ (hg : Good N S B W) {T : TM} {f : ℝ → ℝ} (h : Encl (mkCtx N S B W) T f) :
    (toQModel (mkCtx N S B W) T).asTM.Valid f := by
  rw [toQModel_asTM]
  exact h.valid hg

#print axioms ofBoxes_sound
#print axioms Encl.validQ

end ThomsonCompact.Packed
