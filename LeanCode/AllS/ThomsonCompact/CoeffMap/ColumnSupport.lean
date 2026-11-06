import ThomsonCompact.CoeffMap.RFCore
import ThomsonCompact.CoeffMap.RFDen
import AllS.Units.N_FI.N_kernels.RFColumnBridge

/-!
# Support for the generated D12 scalar-column modules (F2b a)

* `rfRawColumn_eq`: an old raw column built from decoded records over a raw basis is a `Fin`-sum of record
  values times basis polynomials.
* `rec_den`, `rec_scaleD` (by `rfl`) for the shared denominators of `RFDen`; `den_table` (checked once).
* `definedAt_of_den`: a record is defined at `a` as soon as its shared denominator polynomial does not vanish.
-/

namespace ThomsonCompact.CoeffMap.D12RF

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.Packed

theorem rfRawColumn_eq (a : ℝ) (n : ℕ) (rs : Fin n → RFRec) (f : Fin n → Poly3) :
    RFBridge.rfRawColumn a ((List.finRange n).map fun u => (rs u).toRatFun) ((List.finRange n).map f) =
      ∑ u, MvPolynomial.C ((rs u).value a) * f u := by
  simp only [RFBridge.rfRawColumn, List.zipWith_map, List.zipWith_self, RFRec.eval_toRatFun]
  rw [Fin.sum_univ_def]

theorem rec_den (k : Nat) : (rec k).den = denPoly (denIdx k) := rfl
theorem rec_scaleD (k : Nat) : (rec k).scaleD = denScale (denIdx k) := rfl

theorem denTableOk_spec : ∀ n, denTableOk n = true → ∀ k, k < n → denIdx k < nDen ∧ 0 < denScale (denIdx k)
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    simp only [denTableOk, Bool.and_eq_true, Nat.blt_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact denTableOk_spec n h.1.1 k hk
    · exact ⟨h.1.2, h.2⟩

theorem den_table_check : denTableOk nRec = true := by decide +kernel

/-- Every record points to one of the `nDen` denominators, all with nonzero scale (checked once). -/
theorem den_table : ∀ k, k < nRec → denIdx k < nDen ∧ 0 < denScale (denIdx k) :=
  denTableOk_spec nRec den_table_check

theorem definedAt_of_den (a : ℝ) (hden : ∀ d, d < nDen → evalZ (denPoly d) a ≠ 0) :
    ∀ k, k < nRec → (rec k).toRatFun.DefinedAt a := by
  intro k hk
  obtain ⟨h1, h2⟩ := den_table k hk
  rw [RFRec.definedAt_iff, rec_den, rec_scaleD]
  have hs : (denScale (denIdx k) : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  exact div_ne_zero (hden _ h1) hs

#print axioms den_table
#print axioms definedAt_of_den

end ThomsonCompact.CoeffMap.D12RF
