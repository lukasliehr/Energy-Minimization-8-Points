import ThomsonCompact.Fixed.D12c.OldKernel
import ThomsonCompact.Fixed.SoundT

/-!
# Identification with the old literal tables: soundness (workstream F4c)

The decoders of `OldKernel` agree with `recCoeffs`/`decPolysC`/`decPolyVecC`/`lookC`/`dzC`, so a passing
`rowsOldOk` leaf gives `hC sl k i = old k i` (exact coefficient lists) on all covered columns.
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

theorem decAcc_eq (w b : Nat) : ∀ (L y : Nat) (acc : List Int),
    decAcc w (2 ^ w - 1) b L y acc = ((digitsN w L y).map (fun s : ℕ => (s : ℤ) - (b : ℤ))).reverse ++ acc
  | 0, y, acc => by simp [decAcc, digitsN]
  | L + 1, y, acc => by
    show decAcc w (2 ^ w - 1) b L (Nat.shiftRight y w) (Int.subNatNat (Nat.land y (2 ^ w - 1)) b :: acc) = _
    have hm : Nat.land y (2 ^ w - 1) = y % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod y w
    have hs : Nat.shiftRight y w = y / 2 ^ w := Nat.shiftRight_eq_div_pow y w
    rw [decAcc_eq w b L, digitsN_succ, hm, hs, Int.subNatNat_eq_coe]
    simp

theorem recK_eq (x : Nat) : recK x = recCoeffs x := by
  have e0 : ∀ n : Nat, Nat.shiftLeft 1 n = 2 ^ n := fun n => Nat.one_shiftLeft n
  have e1 : Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 20) 255)) 1 = 2 ^ hdrW x - 1 := by
    show Nat.shiftLeft 1 (hdrW x) - 1 = 2 ^ hdrW x - 1
    rw [e0]
  have e2 : Nat.shiftLeft 1 (Nat.sub (Nat.land (Nat.shiftRight x 20) 255) 1) = 2 ^ (hdrW x - 1) := e0 _
  unfold recK
  rw [e1, e2]
  show decAcc (hdrW x) (2 ^ hdrW x - 1) (2 ^ (hdrW x - 1)) (hdrL x) (Nat.shiftRight x 28) [] = _
  rw [decAcc_eq, List.append_nil, recCoeffs, List.map_reverse]
  congr 1

theorem decPolysK_eq : ∀ (n x : Nat), decPolysK n x = decPolysC n x
  | 0, _ => rfl
  | n + 1, x => by
    show (Nat.land x 4095, recK x) :: decPolysK n (Nat.shiftRight x (polyLen x)) =
      (Nat.land x 4095, recCoeffs x) :: decPolysC n (Nat.shiftRight x (polyLen x))
    rw [recK_eq, decPolysK_eq n]

theorem decPolyVecK_eq (ch : Nat → Nat) : ∀ (n c : Nat), decPolyVecK ch n c = decPolyVecC ch n c
  | 0, _ => rfl
  | n + 1, c => by
    show decPolysK (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVecK ch n (Nat.add c 1) =
      decPolysC (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVecC ch n (c + 1)
    rw [decPolysK_eq, decPolyVecK_eq ch n]

theorem lookK_eq : ∀ (l : List (Nat × List Int)) (i : Nat), lookK l i = lookC l i
  | [], _ => rfl
  | e :: es, i => by
    show Bool.rec (lookK es i) e.2 (Nat.beq e.1 i) = ((List.find? (fun e => decide (e.1 = i)) (e :: es)).map Prod.snd).getD []
    rw [List.find?_cons]
    by_cases h : e.1 = i
    · have hb : Nat.beq e.1 i = true := by rw [h]; exact Nat.beq_refl i
      rw [hb]
      simp [h]
    · have hb : Nat.beq e.1 i = false := by
        cases hq : Nat.beq e.1 i
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h
      rw [hb]
      simp only [h, decide_false]
      exact lookK_eq es i

theorem zlEq_eq : ∀ (l l' : List Int), zlEq l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zlEq] at h
  | _ :: _, [], h => by simp [zlEq] at h
  | a :: as, b :: bs, h => by
    have h' : (decide (a = b) && zlEq as bs) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    rw [h'.1, zlEq_eq as bs h'.2]

theorem natRec_all (f : Nat → Bool) : ∀ m, Nat.rec (motive := fun _ => Bool) true (fun p ih => ih && f p) m = true →
    ∀ p, p < m → f p = true
  | 0, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | m + 1, h, p, hp => by
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun p ih => ih && f p) m && f m) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact natRec_all f m h'.1 p hp
    · exact h'.2

theorem rowOldOk_spec (S : Slice) (k : Nat) (old : Nat → List Int) (h : rowOldOk S k old = true) :
    ∀ p, p < S.len → lookC (hrowC S k) (S.i0 + p) = old (S.i0 + p) := by
  intro p hp
  have h1 := natRec_all (fun p => zlEq (lookK (decPolyVecK (S.hc k) (S.hn k) 0) (Nat.add S.i0 p)) (old (Nat.add S.i0 p)))
    S.len h p hp
  have h2 := zlEq_eq _ _ h1
  rw [lookK_eq, decPolyVecK_eq] at h2
  exact h2

theorem listRec_all (f : Slice → Bool) : ∀ l : List Slice,
    List.rec (motive := fun _ => Bool) true (fun S _ ih2 => f S && ih2) l = true → ∀ S ∈ l, f S = true
  | [], _, S, hS => by simp at hS
  | T :: Ts, h, S, hS => by
    have h' : (f T && List.rec (motive := fun _ => Bool) true (fun S _ ih2 => f S && ih2) Ts) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hS with rfl | hS'
    · exact h'.1
    · exact listRec_all f Ts h'.2 S hS'

theorem rowsOldOk_spec (sl : List Slice) (old : Nat → Nat → List Int) :
    ∀ (m k0 : Nat), rowsOldOk sl old m k0 = true → ∀ k, k0 ≤ k → k < k0 + m → ∀ S ∈ sl, rowOldOk S k (old k) = true
  | 0, k0, _, k, h1, h2, _, _ => absurd h2 (by omega)
  | m + 1, k0, h, k, h1, h2, S, hS => by
    have h' : (List.rec (motive := fun _ => Bool) true (fun S _ ih2 => rowOldOk S k0 (old k0) && ih2) sl &&
        rowsOldOk sl old m (Nat.add k0 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with hk | hlt
    · subst hk
      exact listRec_all (fun S => rowOldOk S k0 (old k0)) sl h'.1 S hS
    · exact rowsOldOk_spec sl old m (k0 + 1) (h'.2 : rowsOldOk sl old m (k0 + 1) = true) k (by omega) (by omega) S hS

/-- **Identification of the stored `H` entries** with old literal rows. -/
theorem hC_old (sl : List Slice) (n : Nat) (old : Nat → Nat → List Int)
    (cover : ∀ i, i < n → ∃ S ∈ sl, S.i0 ≤ i ∧ i < S.i0 + S.len)
    (hrows : ∀ k, k < n → ∀ S ∈ sl, rowOldOk S k (old k) = true) :
    ∀ k i, k < n → i < n → hC sl k i = old k i := by
  intro k i hk hi
  obtain ⟨hS, h1, h2⟩ := findSlice_spec sl i (cover i hi)
  have := rowOldOk_spec (findSlice sl i) k (old k) (hrows k hk _ hS) (i - (findSlice sl i).i0) (by omega)
  rw [show (findSlice sl i).i0 + (i - (findSlice sl i).i0) = i by omega] at this
  exact this

theorem dzK_eq (G : GTab) (k : Nat) : dzK G k = lookC (decPolyVecC G.dzc G.dzn 0) (fld (G.inf k) 320 16) := by
  unfold dzK
  rw [lookK_eq, decPolyVecK_eq]

#print axioms hC_old
#print axioms dzK_eq

end ThomsonCompact.Fixed
