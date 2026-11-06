import ThomsonNegative.Geometry.Interpolation

noncomputable section


/-! Root-authorized implementation repair: exact repeated monic deflation replaces
an auxiliary complete-homogeneous polynomial construction. The source confluent
recurrence and its repeated-node factorial branch remain the same. -/
open scoped BigOperators
namespace ThomsonNegative.Geometry

def polynomialDeflate (x : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P /ₘ (Polynomial.X-Polynomial.C x)

theorem polynomialDeflate_decomposition (x : ℝ) (P : Polynomial ℝ) :
    P = Polynomial.C (P.eval x)+(Polynomial.X-Polynomial.C x)*polynomialDeflate x P := by
  have h := (Polynomial.modByMonic_add_div P (Polynomial.X-Polynomial.C x)).symm
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  exact h

theorem polynomialDeflate_eval_relation (x y : ℝ) (P : Polynomial ℝ) :
    P.eval y = P.eval x+(y-x)*(polynomialDeflate x P).eval y := by
  have h := congrArg (Polynomial.eval y) (polynomialDeflate_decomposition x P)
  simpa only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X] using h

theorem polynomialDeflate_eval_swap (x y : ℝ) (P : Polynomial ℝ) :
    (polynomialDeflate x P).eval y = (polynomialDeflate y P).eval x := by
  by_cases hxy : x = y
  · subst y; rfl
  have h₁ := polynomialDeflate_eval_relation x y P
  have h₂ := polynomialDeflate_eval_relation y x P
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hxy))
  nlinarith [h₁, h₂]

theorem polynomialDeflate_commute (x y : ℝ) (P : Polynomial ℝ) :
    polynomialDeflate x (polynomialDeflate y P) = polynomialDeflate y (polynomialDeflate x P) := by
  have hX := polynomialDeflate_decomposition x P
  have hY := polynomialDeflate_decomposition y P
  have hXY := polynomialDeflate_decomposition y (polynomialDeflate x P)
  have hYX := polynomialDeflate_decomposition x (polynomialDeflate y P)
  rw [← polynomialDeflate_eval_swap x y P] at hYX
  have hC := congrArg (Polynomial.C : ℝ → Polynomial ℝ) (polynomialDeflate_eval_relation x y P)
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_sub] at hC
  apply mul_left_cancel₀
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero x) (Polynomial.X_sub_C_ne_zero y))
  linear_combination hX-hY+(Polynomial.X-Polynomial.C x)*hXY-
    (Polynomial.X-Polynomial.C y)*hYX-hC

theorem polynomialDeflate_difference (x y : ℝ) (P : Polynomial ℝ) :
    polynomialDeflate x P-polynomialDeflate y P =
      Polynomial.C (x-y)*polynomialDeflate x (polynomialDeflate y P) := by
  have hXY := polynomialDeflate_decomposition y (polynomialDeflate x P)
  have hYX := polynomialDeflate_decomposition x (polynomialDeflate y P)
  rw [← polynomialDeflate_eval_swap x y P] at hYX
  rw [← polynomialDeflate_commute x y P] at hXY
  rw [Polynomial.C_sub]
  linear_combination hXY-hYX

theorem polynomialDeflate_taylor_coeff (x : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (Polynomial.taylor x (polynomialDeflate x P)).coeff n = (Polynomial.taylor x P).coeff (n+1) := by
  have h := congrArg (Polynomial.taylor x) (polynomialDeflate_decomposition x P)
  simp only [map_add, Polynomial.taylor_C, Polynomial.taylor_mul, map_sub,
    Polynomial.taylor_X, add_sub_cancel_right] at h
  have hc := congrArg (fun Q : Polynomial ℝ => Q.coeff (n+1)) h
  simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Nat.add_one_ne_zero, ite_false,
    Polynomial.coeff_X_mul, zero_add] using hc.symm

theorem polynomialDeflate_iterate_taylor_coeff (x : ℝ) (P : Polynomial ℝ) (k n : ℕ) :
    (Polynomial.taylor x ((polynomialDeflate x)^[k] P)).coeff n =
      (Polynomial.taylor x P).coeff (n+k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', polynomialDeflate_taylor_coeff, ih]
    congr 1
    omega

theorem polynomialDeflate_iterate_eval (x : ℝ) (P : Polynomial ℝ) (k : ℕ) :
    ((polynomialDeflate x)^[k] P).eval x =
      ((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℝ) := by
  have h := polynomialDeflate_iterate_taylor_coeff x P k 0
  simp only [zero_add, Polynomial.taylor_coeff, Polynomial.hasseDeriv_zero, LinearMap.id_apply] at h
  rw [h, eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  have hf := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := k)) P
  have hev := congrArg (Polynomial.eval x) hf
  change (k.factorial • Polynomial.hasseDeriv k P).eval x =
    ((Polynomial.derivative^[k]) P).eval x at hev
  simpa only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, mul_comm] using hev

theorem newton_hermite_divided_difference_monomials (x y : ℝ) (P : Polynomial ℝ) :
    (polynomialDeflate x P).eval y = (polynomialDeflate y P).eval x ∧
    polynomialDeflate x (polynomialDeflate y P) = polynomialDeflate y (polynomialDeflate x P) ∧
    polynomialDeflate x P-polynomialDeflate y P =
      Polynomial.C (x-y)*polynomialDeflate x (polynomialDeflate y P) ∧
    ∀ k : ℕ, ((polynomialDeflate x)^[k] P).eval x =
      ((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℝ) :=
  ⟨polynomialDeflate_eval_swap x y P, polynomialDeflate_commute x y P,
    polynomialDeflate_difference x y P, polynomialDeflate_iterate_eval x P⟩

end ThomsonNegative.Geometry


open scoped BigOperators
namespace ThomsonNegative.Geometry

def polynomialJets (P : Polynomial ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.derivative^[k]) P).eval x

def polynomialDeflateBlock (z : ℕ → ℝ) (start : ℕ) : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, P => P
  | k+1, P => polynomialDeflate (z (start+k)) (polynomialDeflateBlock z start k P)

def polynomialDD (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ) : ℝ :=
  (polynomialDeflateBlock z start k P).eval (z (start+k))

def confluentTable (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ
  | 0, start => J 0 (z start)
  | k+1, start => if z (start+k+1) = z start then
      J (k+1) (z start) / ((k+1).factorial : ℝ)
    else (confluentTable z J k (start+1)-confluentTable z J k start) /
      (z (start+k+1)-z start)

def GroupedPrefix (z : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ start k, start+k < N → z (start+k) = z start →
    ∀ j ≤ k, z (start+j) = z start

theorem polynomialDeflateBlock_commute (z : ℕ → ℝ) (start k : ℕ) (x : ℝ) (P : Polynomial ℝ) :
    polynomialDeflateBlock z start k (polynomialDeflate x P) =
      polynomialDeflate x (polynomialDeflateBlock z start k P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [polynomialDeflateBlock, ih]
    exact polynomialDeflate_commute (z (start+k)) x _

theorem polynomialDeflateBlock_head (z : ℕ → ℝ) (start k : ℕ) (P : Polynomial ℝ) :
    polynomialDeflateBlock z start (k+1) P =
      polynomialDeflateBlock z (start+1) k (polynomialDeflate (z start) P) := by
  induction k with
  | zero => simp [polynomialDeflateBlock]
  | succ k ih =>
    change polynomialDeflate (z (start+(k+1))) (polynomialDeflateBlock z start (k+1) P) =
      polynomialDeflate (z ((start+1)+k))
        (polynomialDeflateBlock z (start+1) k (polynomialDeflate (z start) P))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (polynomialDeflate (z (start+(k+1)))) ih

theorem polynomialDD_rotate (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ) :
    polynomialDD z P k start = (polynomialDeflateBlock z (start+1) k P).eval (z start) := by
  cases k with
  | zero => simp [polynomialDD, polynomialDeflateBlock]
  | succ k =>
    rw [polynomialDD, polynomialDeflateBlock_head, polynomialDeflateBlock_commute,
      polynomialDeflate_eval_swap]
    simp only [polynomialDeflateBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem polynomialDD_secant (z : ℕ → ℝ) (P : Polynomial ℝ) (k start : ℕ)
    (hne : z (start+k+1) ≠ z start) :
    polynomialDD z P (k+1) start =
      (polynomialDD z P k (start+1)-polynomialDD z P k start)/(z (start+k+1)-z start) := by
  rw [polynomialDD_rotate z P k start]
  rw [polynomialDD, polynomialDeflateBlock_head, polynomialDeflateBlock_commute]
  have h := polynomialDeflate_eval_relation (z start) (z (start+k+1))
    (polynomialDeflateBlock z (start+1) k P)
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  simp only [polynomialDD]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (show (polynomialDeflate (z start) (polynomialDeflateBlock z (start+1) k P)).eval
      (z (start+k+1)) * (z (start+k+1)-z start) =
      (polynomialDeflateBlock z (start+1) k P).eval (z (start+k+1)) -
      (polynomialDeflateBlock z (start+1) k P).eval (z start) by nlinarith [h])

theorem polynomialDeflateBlock_constant (z : ℕ → ℝ) (start k : ℕ) (x : ℝ)
    (P : Polynomial ℝ) (hz : ∀ j < k, z (start+j) = x) :
    polynomialDeflateBlock z start k P = (polynomialDeflate x)^[k] P := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [polynomialDeflateBlock, hz k (by omega), ih (fun j hj => hz j (by omega)),
      Function.iterate_succ_apply']

theorem confluentTable_polynomialDD (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) (k start : ℕ) (hbound : start+k < N) :
    confluentTable z (polynomialJets P) k start = polynomialDD z P k start := by
  induction k generalizing start with
  | zero => simp [confluentTable, polynomialDD, polynomialDeflateBlock, polynomialJets]
  | succ k ih =>
    rw [confluentTable]
    split_ifs with he
    · have hall : ∀ j ≤ k+1, z (start+j) = z start :=
        hz start (k+1) hbound (by simpa only [Nat.add_assoc] using he)
      rw [polynomialDD, polynomialDeflateBlock_constant z start (k+1) (z start) P
        (fun j hj => hall j (by omega)), hall (k+1) le_rfl]
      exact (polynomialDeflate_iterate_eval (z start) P (k+1)).symm
    · rw [ih (start+1) (by omega), ih start (by omega)]
      exact (polynomialDD_secant z P k start he).symm

theorem newtonBasis_succ (z : ℕ → ℝ) (N : ℕ) :
    newtonBasis z (N+1) = newtonBasis z N*(Polynomial.X-Polynomial.C (z N)) := by
  exact Finset.prod_range_succ _ N

theorem polynomial_newton_remainder (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ) :
    P = (∑ i ∈ Finset.range N, Polynomial.C (polynomialDD z P i 0)*newtonBasis z i) +
      newtonBasis z N*polynomialDeflateBlock z 0 N P := by
  induction N with
  | zero => simp [newtonBasis, polynomialDeflateBlock]
  | succ N ih =>
    rw [Finset.sum_range_succ, newtonBasis_succ, polynomialDeflateBlock]
    have h := polynomialDeflate_decomposition (z N) (polynomialDeflateBlock z 0 N P)
    simp only [polynomialDD, zero_add] at ih ⊢
    linear_combination ih+newtonBasis z N*h

theorem polynomialDeflate_degree_lt (x : ℝ) (P : Polynomial ℝ) (n : ℕ)
    (h : P.degree < (n+1 : ℕ)) : (polynomialDeflate x P).degree < n := by
  by_cases hP : P = 0
  · simp [hP, polynomialDeflate]
  have hn : P.natDegree < n+1 := by
    rw [Polynomial.degree_eq_natDegree hP] at h
    exact_mod_cast h
  have hle : P.degree ≤ (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hP]
    exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hn)
  exact (Polynomial.degree_divByMonic_lt P (Polynomial.X-Polynomial.C x) hP (by simp)).trans_le hle

theorem polynomialDeflateBlock_zero (z : ℕ → ℝ) (P : Polynomial ℝ) (N start : ℕ)
    (h : P.degree < N) : polynomialDeflateBlock z start N P = 0 := by
  induction N generalizing P start with
  | zero => exact Polynomial.degree_eq_bot.mp (WithBot.lt_coe_bot.mp h)
  | succ N ih =>
    rw [polynomialDeflateBlock_head]
    exact ih _ _ (polynomialDeflate_degree_lt (z start) P N h)

theorem newton_hermite_polynomial_newton (z : ℕ → ℝ) (P : Polynomial ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) (hP : P.degree < N) :
    P = ∑ i ∈ Finset.range N, Polynomial.C (confluentTable z (polynomialJets P) i 0)*newtonBasis z i := by
  have h := polynomial_newton_remainder z P N
  rw [polynomialDeflateBlock_zero z P N 0 hP, mul_zero, add_zero] at h
  calc
    P = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [confluentTable_polynomialDD z P N hz i 0 (by simpa using Finset.mem_range.mp hi)]

end ThomsonNegative.Geometry


open scoped BigOperators
namespace ThomsonNegative.Geometry

def sourceNewtonPolynomial (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N, Polynomial.C (confluentTable z J i 0)*newtonBasis z i

def sourceNewtonHorner (z : ℕ → ℝ) (c : ℕ → ℝ) : ℕ → ℕ → Polynomial ℝ
  | 0, _ => 0
  | N+1, start => Polynomial.C (c start)+(Polynomial.X-Polynomial.C (z start))*
      sourceNewtonHorner z c N (start+1)

theorem priorMultiplicity_of_window (z : ℕ → ℝ) (N start k : ℕ) (x : ℝ)
    (hbound : start+k < N) (hall : ∀ j ≤ k, z (start+j) = x) :
    k < priorMultiplicity z N x := by
  classical
  have hsub : Finset.Icc start (start+k) ⊆ (Finset.range N).filter (fun i => z i = x) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · have h := hall (i-start) (by omega)
      simpa only [Nat.add_sub_of_le hi'.1] using h
  have hcard := Finset.card_le_card hsub
  have hc : (Finset.Icc start (start+k)).card = k+1 := by simp only [Nat.card_Icc]; omega
  rw [hc] at hcard
  exact Nat.lt_of_succ_le hcard

theorem confluentTable_congr_jets (z : ℕ → ℝ) (J K : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N)
    (hJK : ∀ x k, k < priorMultiplicity z N x → J k x = K k x)
    (k start : ℕ) (hbound : start+k < N) :
    confluentTable z J k start = confluentTable z K k start := by
  induction k generalizing start with
  | zero =>
    apply hJK
    exact priorMultiplicity_of_window z N start 0 (z start) hbound
      (by
        intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        simp only [hj0, Nat.add_zero])
  | succ k ih =>
    simp only [confluentTable]
    split_ifs with he
    · rw [hJK (z start) (k+1)
        (priorMultiplicity_of_window z N start (k+1) (z start) hbound
          (hz start (k+1) hbound (by simpa only [Nat.add_assoc] using he)))]
    · rw [ih (start+1) (by omega), ih start (by omega)]

theorem sourceNewtonPolynomial_eq (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) : sourceNewtonPolynomial z J N = newtonHermite z J N := by
  symm
  have hstage := newton_hermite_stage_invariant z J N
  calc
    newtonHermite z J N = ∑ i ∈ Finset.range N,
        Polynomial.C (confluentTable z (polynomialJets (newtonHermite z J N)) i 0)*newtonBasis z i :=
      newton_hermite_polynomial_newton z _ N hz hstage.1
    _ = sourceNewtonPolynomial z J N := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [confluentTable_congr_jets z (polynomialJets (newtonHermite z J N)) J N hz
        hstage.2 i 0 (by simpa using Finset.mem_range.mp hi)]

@[simp] theorem newtonBasis_zero (z : ℕ → ℝ) : newtonBasis z 0 = 1 := by simp [newtonBasis]

theorem shifted_newtonBasis_succ (z : ℕ → ℝ) (start i : ℕ) :
    newtonBasis (fun k => z (start+k)) (i+1) =
      newtonBasis (fun k => z (start+1+k)) i*(Polynomial.X-Polynomial.C (z start)) := by
  simp only [newtonBasis, Finset.prod_range_succ', Nat.add_zero,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sourceNewtonHorner_eq_sum (z : ℕ → ℝ) (c : ℕ → ℝ) (N start : ℕ) :
    sourceNewtonHorner z c N start = ∑ i ∈ Finset.range N,
      Polynomial.C (c (start+i))*newtonBasis (fun k => z (start+k)) i := by
  induction N generalizing start with
  | zero => simp [sourceNewtonHorner]
  | succ N ih =>
    rw [sourceNewtonHorner, ih, Finset.sum_range_succ']
    simp_rw [shifted_newtonBasis_succ]
    simp only [newtonBasis_zero, Nat.add_zero, mul_one, ← mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Finset.sum_mul]
    ring

theorem sourceNewtonHorner_eq (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ) :
    sourceNewtonHorner z (fun i => confluentTable z J i 0) N 0 = sourceNewtonPolynomial z J N := by
  simpa only [sourceNewtonPolynomial, Nat.zero_add] using
    sourceNewtonHorner_eq_sum z (fun i => confluentTable z J i 0) N 0

theorem newton_hermite_confluent_bridge (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (N : ℕ)
    (hz : GroupedPrefix z N) :
    sourceNewtonPolynomial z J N = newtonHermite z J N ∧
    sourceNewtonHorner z (fun i => confluentTable z J i 0) N 0 = newtonHermite z J N :=
  ⟨sourceNewtonPolynomial_eq z J N hz,
    (sourceNewtonHorner_eq z J N).trans (sourceNewtonPolynomial_eq z J N hz)⟩

end ThomsonNegative.Geometry
namespace ThomsonNegative.Geometry
lemma doubleNode_grouped (z : Fin 4 → ℝ) (hz : Function.Injective z) :
    GroupedPrefix (doubleNode z) 8 := by
  intro start k hk he j hj
  unfold doubleNode at he ⊢
  have hv := congrArg Fin.val (hz he)
  have h0 : start/2 < 4 := by omega
  have h1 : (start+k)/2 < 4 := by omega
  have h2 : (start+j)/2 < 4 := by omega
  simp only [Fin.val_mk,Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1] at hv
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk,Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h2]
  omega

theorem sourceNewtonHorner_hermiteH7 (q : ℝ) (z : Fin 4 → ℝ) (hz : Function.Injective z) :
    sourceNewtonHorner (doubleNode z)
      (fun i => confluentTable (doubleNode z) (Analytic.auxiliaryTJet q) i 0) 8 0 = hermiteH7 q z :=
  (newton_hermite_confluent_bridge (doubleNode z) (Analytic.auxiliaryTJet q) 8 (doubleNode_grouped z hz)).2
#print axioms sourceNewtonHorner_hermiteH7
end ThomsonNegative.Geometry
