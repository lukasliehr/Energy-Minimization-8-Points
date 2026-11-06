import ThomsonCompact.CoeffMap.Deg.DotSound
import ThomsonCompact.CoeffMap.Deg.DenseSound

/-!
# Batched dot products are the single dot products (F2f)

`bdot_eq`: if the batch check `bdotOk` passes, output `i` of `bdot c as Bs n` is **equal** (as a TM) to
`dotTM c [(aⱼ, Bⱼᵢ)]ⱼ`, so `dotTM_sound` applies to it. The packed sums of `bdotAcc` are
`Σ_{i<n} (dotAcc of output i)ₖ 2^(sp i)` (`bdotAcc_fields`, exact identities of natural numbers); the field bounds
`< 2^K` and `< 2^16` terms keep every slot below `2^(2K+20)`, so slot extraction (`slot_digits`) returns the
accumulators of output `i`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

theorem packN_eq (sp : ℕ) : ∀ xs : List ℕ, packN sp xs = Nat.ofDigits (2 ^ sp) xs
  | [] => rfl
  | x :: xs => by
    show Nat.add x (Nat.shiftLeft (packN sp xs) sp) = _
    rw [Nat.ofDigits_cons, packN_eq sp xs, shl_eq, Nat.add_eq]
    ring

theorem packN_sum (sp n : ℕ) (f : TM → ℕ) (B : List TM) (hB : B.length = n) :
    packN sp (B.map f) = ∑ i ∈ Finset.range n, f (B.getD i zeroTM) * 2 ^ (sp * i) := by
  rw [packN_eq, sum_digits_eq sp (fun i => f (B.getD i zeroTM)) n]
  congr 1
  apply List.ext_getElem
  · simp [hB]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- The accumulators of output `i`. -/
noncomputable def bAcc (as : List TM) (Bs : List (List TM)) (i : ℕ) : ℕ × ℕ × ℕ × ℕ × Bool :=
  dotAcc ((as.zip Bs).map fun p => (p.1, p.2.getD i zeroTM))

theorem bdotAcc_fields (sp n : ℕ) : ∀ (as : List TM) (Bs : List (List TM)), (∀ B ∈ Bs, B.length = n) →
    (bdotAcc sp as Bs).1 = ∑ i ∈ Finset.range n, (bAcc as Bs i).1 * 2 ^ (sp * i) ∧
    (bdotAcc sp as Bs).2.1 = ∑ i ∈ Finset.range n, (bAcc as Bs i).2.1 * 2 ^ (sp * i) ∧
    (bdotAcc sp as Bs).2.2.1 = ∑ i ∈ Finset.range n, (bAcc as Bs i).2.2.1 * 2 ^ (sp * i) ∧
    (bdotAcc sp as Bs).2.2.2 = ∑ i ∈ Finset.range n, (bAcc as Bs i).2.2.2.1 * 2 ^ (sp * i)
  | [], Bs, _ => by simp [bdotAcc, bAcc, dotAcc_nil]
  | a :: as, [], _ => by simp [bdotAcc, bAcc, dotAcc_nil]
  | a :: as, B :: Bs, hB => by
    obtain ⟨h1, h2, h3, h4⟩ := bdotAcc_fields sp n as Bs (fun B' hB' => hB B' (List.mem_cons_of_mem _ hB'))
    have hBn := hB B (List.mem_cons_self ..)
    have e : bdotAcc sp (a :: as) (B :: Bs) =
        (a.v * packN sp (B.map TM.v) + (bdotAcc sp as Bs).1, a.a * packN sp (B.map TM.a) + (bdotAcc sp as Bs).2.1,
          a.s * packN sp (B.map TM.e) + a.e * packN sp (B.map TM.s) + a.e * packN sp (B.map TM.e) +
            (bdotAcc sp as Bs).2.2.1, a.s * packN sp (B.map TM.s) + (bdotAcc sp as Bs).2.2.2) := rfl
    have hb : ∀ i, bAcc (a :: as) (B :: Bs) i = dotAcc ((a, B.getD i zeroTM) ::
        ((as.zip Bs).map fun p => (p.1, p.2.getD i zeroTM))) := fun i => rfl
    simp only [hb, dotAcc_cons, e]
    rw [packN_sum sp n _ B hBn, packN_sum sp n _ B hBn, packN_sum sp n _ B hBn, packN_sum sp n _ B hBn, h1, h2, h3, h4]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [bAcc, Finset.mul_sum, ← Finset.sum_add_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Fields of a TM below `2^K` (and `ok`). -/
def Small (K : ℕ) (T : TM) : Prop := T.ok = true ∧ T.v < 2 ^ K ∧ T.a < 2 ^ K ∧ T.s < 2 ^ K ∧ T.e < 2 ^ K

theorem dotAcc_bound (K : ℕ) : ∀ L : List (TM × TM), (∀ p ∈ L, Small K p.1 ∧ Small K p.2) →
    (dotAcc L).1 ≤ L.length * 2 ^ (2 * K) ∧ (dotAcc L).2.1 ≤ L.length * 2 ^ (2 * K) ∧
    (dotAcc L).2.2.1 ≤ L.length * (3 * 2 ^ (2 * K)) ∧ (dotAcc L).2.2.2.1 ≤ L.length * 2 ^ (2 * K) ∧
    (dotAcc L).2.2.2.2 = true
  | [], _ => by simp [dotAcc_nil]
  | (A, B') :: L, h => by
    obtain ⟨i1, i2, i3, i4, i5⟩ := dotAcc_bound K L (fun p hp => h p (List.mem_cons_of_mem _ hp))
    obtain ⟨⟨ao, av, aa, as, ae⟩, ⟨bo, bv, ba, bs, be⟩⟩ := h (A, B') (List.mem_cons_self ..)
    simp only at ao av aa as ae bo bv ba bs be
    rw [dotAcc_cons, List.length_cons, add_mul, one_mul, add_mul, one_mul]
    have hK : 2 ^ (2 * K) = 2 ^ K * 2 ^ K := by rw [two_mul, pow_add]
    have p1 : A.v * B'.v ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul av.le bv.le
    have p2 : A.a * B'.a ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul aa.le ba.le
    have p3 : A.s * B'.e ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul as.le be.le
    have p4 : B'.s * A.e ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul bs.le ae.le
    have p5 : A.e * B'.e ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul ae.le be.le
    have p6 : A.s * B'.s ≤ 2 ^ (2 * K) := hK ▸ Nat.mul_le_mul as.le bs.le
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    simp [ao, bo, i5]

/-- **A passing batch computes the single dot products.** -/
theorem bdot_eq {N S B W : ℕ} (as : List TM) (Bs : List (List TM)) (n : ℕ) (hB : ∀ B ∈ Bs, B.length = n)
    (hok : bdotOk (mkCtx N S B W) as Bs = true) (i : ℕ) (hi : i < n) :
    listAt zeroTM (bdot (mkCtx N S B W) as Bs n) i =
      dotTM (mkCtx N S B W) ((as.zip Bs).map fun p => (p.1, p.2.getD i zeroTM)) := by
  set K := W * (2 * N + 1) with hKdef
  have htwoK : (mkCtx N S B W).twoK = 2 ^ K := rfl
  have hok' := hok
  unfold bdotOk at hok'
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, htwoK] at hok'
  obtain ⟨⟨hA, hBs⟩, hlen⟩ := hok'
  have hsmall : ∀ j, ∀ p ∈ (as.zip Bs).map (fun p => (p.1, p.2.getD j zeroTM)), j < n → Small K p.1 ∧ Small K p.2 := by
    intro j p hp hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq1 := List.of_mem_zip hq
    have ha := hA q.1 hq1.1
    have hb := hB q.2 hq1.2
    have hT := hBs q.2 hq1.2 (q.2.getD j zeroTM) (by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    exact ⟨⟨ha.1.1.1.1, ha.1.1.1.2, ha.1.1.2, ha.1.2, ha.2⟩, ⟨hT.1.1.1.1, hT.1.1.1.2, hT.1.1.2, hT.1.2, hT.2⟩⟩
  have hzl : ∀ j, ((as.zip Bs).map (fun p => (p.1, p.2.getD j zeroTM))).length < 65536 := by
    intro j
    rw [List.length_map]
    rw [List.length_zip]
    exact lt_of_le_of_lt (min_le_left _ _) hlen
  have hbd : ∀ j, j < n → (bAcc as Bs j).1 < 2 ^ bsp (mkCtx N S B W) ∧ (bAcc as Bs j).2.1 < 2 ^ bsp (mkCtx N S B W) ∧
      (bAcc as Bs j).2.2.1 < 2 ^ bsp (mkCtx N S B W) ∧ (bAcc as Bs j).2.2.2.1 < 2 ^ bsp (mkCtx N S B W) := by
    intro j hj
    obtain ⟨b1, b2, b3, b4, -⟩ := dotAcc_bound K _ (fun p hp => hsmall j p hp hj)
    have hl := hzl j
    have e : 2 ^ bsp (mkCtx N S B W) = 2 ^ 20 * 2 ^ (2 * K) := by
      show 2 ^ (2 * K + 20) = _; rw [pow_add]; ring
    have hpos : 0 < 2 ^ (2 * K) := by positivity
    unfold bAcc
    rw [e]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  obtain ⟨f1, f2, f3, f4⟩ := bdotAcc_fields (bsp (mkCtx N S B W)) n as Bs hB
  have hsp : 0 < bsp (mkCtx N S B W) := by show 0 < 2 * K + 20; omega
  unfold bdot
  rw [listAt_mkList _ _ hi]
  show dotFin _ _ = dotFin _ (bAcc as Bs i)
  congr 1
  rw [f1, f2, f3, f4,
    slot_digits _ hsp _ n i (fun j hj => (hbd j hj).1) hi,
    slot_digits _ hsp _ n i (fun j hj => (hbd j hj).2.1) hi,
    slot_digits _ hsp _ n i (fun j hj => (hbd j hj).2.2.1) hi,
    slot_digits _ hsp _ n i (fun j hj => (hbd j hj).2.2.2) hi, hok]
  have hT := (dotAcc_bound K _ (fun p hp => hsmall i p hp hi)).2.2.2.2
  unfold bAcc at hT ⊢
  generalize dotAcc _ = q at hT ⊢
  obtain ⟨q1, q2, q3, q4, q5⟩ := q
  simp only at hT ⊢
  rw [hT]

#print axioms bdot_eq

end ThomsonCompact.CoeffMap.Deg
