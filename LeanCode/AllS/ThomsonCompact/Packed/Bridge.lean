import ThomsonCompact.Packed.Export
import Blueprint.CAPContracts

/-!
# Bridge to the old Taylor-model semantics

`toTM c T` is the packed TM as a `Blueprint.CAP.TM` with point coefficient boxes `cₖ/2^S` and error `e/2^S`;
`Encl.valid` turns a packed enclosure into the old `TM.Valid`.
-/

namespace ThomsonCompact.Packed

variable {N S B W : ℕ}

/-- The packed TM as an old-style `Blueprint.CAP.TM` (point coefficient boxes). -/
noncomputable def toTM (c : Ctx) (T : TM) : Blueprint.CAP.TM c.N :=
  ⟨fun k => Blueprint.CAP.Box.point ((((decode c T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ c.S), (T.e : ℚ) / 2 ^ c.S⟩

theorem Encl.valid (hg : Good N S B W) {T : TM} {f : ℝ → ℝ} (h : Encl (mkCtx N S B W) T f) :
    (toTM (mkCtx N S B W) T).Valid f := by
  refine ⟨by simp only [toTM]; positivity,
    fun k => (((((decode (mkCtx N S B W) T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ S : ℚ) : ℝ), ?_, ?_⟩
  · intro k
    exact Blueprint.CAP.Box.contains_point _
  · intro x hx
    have hexp := h.export hg x hx
    have hsum : Blueprint.CAP.scalarEval
        (fun k : Fin (N + 1) => (((((decode (mkCtx N S B W) T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ S : ℚ) : ℝ)) x =
        poly (mkCtx N S B W) T x := by
      rw [poly_eq_sum, Blueprint.CAP.scalarEval]
      rw [Fin.sum_univ_eq_sum_range
        (fun k => (((((decode (mkCtx N S B W) T.v).getD k 0 : ℤ) : ℚ) / 2 ^ S : ℚ) : ℝ) * x ^ k) (N + 1)]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rfl
    have herr : (((toTM (mkCtx N S B W) T).error : ℚ) : ℝ) = err (mkCtx N S B W) T := by
      simp only [toTM, err]
      push_cast
      rfl
    show |f x - Blueprint.CAP.scalarEval
        (fun k : Fin (N + 1) => (((((decode (mkCtx N S B W) T.v).getD k.val 0 : ℤ) : ℚ) / 2 ^ S : ℚ) : ℝ)) x| ≤
      (((toTM (mkCtx N S B W) T).error : ℚ) : ℝ)
    rw [hsum, herr]
    exact hexp

#print axioms Encl.valid
#print axioms Encl.export

end ThomsonCompact.Packed
