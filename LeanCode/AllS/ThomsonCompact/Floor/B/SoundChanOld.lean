import ThomsonCompact.Floor.B.SoundChan
import AllS.Units.N_AI.N_matrix_polynomials.N_bernstein_identity

/-!
# The channel values are Bernstein controls (F3b, link to the old Bernstein identity)

* `bernI_eq`: `β̃_ik = D_N · bernsteinTransform N i k` (`D_N = bernDen N`);
* `chanZ_bernstein`: the centre polynomial `Σ_k C_k x^k` of coordinate `m` is `Σ_i (z_i / D) b_i(x)`, with the
  control channel values `z_i` of `chanZ cb m` and the Bernstein weights `b_i` of the old identity
  (`chanZc_bernstein`: the same for `chanZc` on the stored coordinates).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Floor (slot)
open scoped BigOperators

theorem bernI_eq (N k i : ℕ) (hk : k ≤ N) (hi : i ≤ N) :
    (sv (bernI N (bernDen N) i k) : ℝ) = (bernDen N : ℝ) * (Blueprint.CAP.bernsteinTransform N i k : ℝ) := by
  have _ := hi -- (not needed: the identity holds for every `i`)
  have hc : (N.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hdvd : N.choose k ∣ bernDen N := by rw [← chooseF_eq]; exact chooseF_dvd_bernDen N k hk
  rw [sv_bernI, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hc, Blueprint.CAP.bernsteinTransform_formula]
  push_cast
  ring

theorem chanZ_bernstein (cb : CellB) (m : ℕ) (x : ℝ) :
    Blueprint.CAP.scalarEval (N := cb.N) (fun k => (sv (smDec (slot cb.wc (cb.cm m) k.val)) : ℝ)) x =
      ∑ i : Fin (cb.N + 1), (((chanZ cb m).getD i.val 0 : ℤ) : ℝ) / (cb.D : ℝ) *
        Blueprint.CAP.bernsteinWeight cb.N i.val x := by
  have hD : (cb.D : ℝ) ≠ 0 := by exact_mod_cast (bernDen_pos cb.N).ne'
  rw [Blueprint.CAP.matrix_polynomials_bernstein_identity cb.N _ x]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have e := Fin.sum_univ_eq_sum_range (fun k => (Blueprint.CAP.bernsteinTransform cb.N i.val k : ℝ) *
    ((sv (smDec (slot cb.wc (cb.cm m) k)) : ℤ) : ℝ)) (cb.N + 1)
  rw [e, chanZ_getD_ctl cb m i.val i.isLt, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hD' : (bernDen cb.N : ℝ) ≠ 0 := hD
  rw [Int.cast_mul, show cb.D = bernDen cb.N from rfl, bernI_eq cb.N k i.val (by omega) (by omega)]
  field_simp

theorem chanZc_bernstein (cb : CellB) (m : ℕ) (hm : m < cb.cvc.length) (x : ℝ) :
    Blueprint.CAP.scalarEval (N := cb.N) (fun k => (sv (smDec (slot cb.wc (cb.cm m) k.val)) : ℝ)) x =
      ∑ i : Fin (cb.N + 1), (((chanZc cb m).getD i.val 0 : ℤ) : ℝ) / (cb.D : ℝ) *
        Blueprint.CAP.bernsteinWeight cb.N i.val x := by
  rw [chanZc_of_lt cb hm]
  exact chanZ_bernstein cb m x

end ThomsonCompact.Floor.B
