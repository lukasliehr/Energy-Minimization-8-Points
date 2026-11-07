import ThomsonNegative.Analytic.Rolle
import ThomsonNegative.Auxiliary

/-!
The degree-seven Hermite minorant at four double contacts. The proof uses the
new auxiliary potential directly and a generic repeated-node Rolle theorem;
it does not import the positive-s certificate or a numerical matrix witness.
-/

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative.Analytic

/-- Products in the higher derivatives of A. -/
def risingCoeff (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => risingCoeff q n*(q+n+1)

/-- Derivative tower of the auxiliary potential in x. -/
def auxiliaryJet (q : ℝ) : ℕ → ℝ → ℝ
  | 0 => normalizedAux q
  | 1 => auxSlope q
  | n+2 => fun x => risingCoeff q n*(1-x)^(-q-1-n)

lemma auxiliaryJet_hasDerivAt (q x : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hx : x < 1) (k : ℕ) :
    HasDerivAt (auxiliaryJet q k) (auxiliaryJet q (k+1) x) x := by
  rcases k with _ | k
  · exact normalizedAux_hasDerivAt q x hq hx
  rcases k with _ | n
  · simpa [auxiliaryJet,risingCoeff] using auxSlope_hasDerivAt q x hq.1.ne' hx
  · have hbase := (hasDerivAt_id x).const_sub 1
    have hp := (Real.hasDerivAt_rpow_const (p := -q-1-(n:ℝ))
      (Or.inl (show 1-x ≠ 0 by linarith))).comp x hbase
    have hh := hp.const_mul (risingCoeff q n)
    convert! hh using 1
    simp only [auxiliaryJet,risingCoeff,Nat.cast_add,Nat.cast_one]
    rw [show -q-1-((n:ℝ)+1)=(-q-1-n)-1 by ring]
    ring

lemma risingCoeff_ge_factorial (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    (n.factorial:ℝ) ≤ risingCoeff q n := by
  induction n with
  | zero => norm_num [risingCoeff]
  | succ n ih =>
    have hc : 0 ≤ risingCoeff q n := (by positivity : (0:ℝ) ≤ n.factorial).trans ih
    have h := mul_le_mul ih (show (n:ℝ)+1 ≤ q+n+1 by linarith)
      (by positivity : (0:ℝ) ≤ (n:ℝ)+1) hc
    simpa [risingCoeff,Nat.factorial_succ,mul_comm] using h

lemma auxiliaryJet_eight_lower (q x : ℝ) (hq : 0 ≤ q)
    (hx : x ∈ Set.Ico (0:ℝ) 1) : 720 ≤ auxiliaryJet q 8 x := by
  have hc := risingCoeff_ge_factorial q hq 6
  norm_num at hc
  have hp : 1 ≤ (1-x)^(-q-1-(6:ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith [hx.2])
      (by linarith [hx.1]) (by linarith)
  change 720 ≤ risingCoeff q 6*(1-x)^(-q-1-(6:ℝ))
  nlinarith

/-- The potential in the geometric inner-product variable t. -/
def auxiliaryT (q t : ℝ) : ℝ := normalizedAux q ((1+t)/2)

def auxiliaryTJet (q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  auxiliaryJet q k ((1+t)/2)/(2:ℝ)^k

lemma auxiliaryTJet_hasDerivAt (q t : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ht : t < 1) (k : ℕ) :
    HasDerivAt (auxiliaryTJet q k) (auxiliaryTJet q (k+1) t) t := by
  have harg : HasDerivAt (fun y : ℝ => (1+y)/2) (1/2) t := by
    convert! ((hasDerivAt_id t).const_add 1).div_const 2 using 1
  have hh := ((auxiliaryJet_hasDerivAt q ((1+t)/2) hq (by linarith) k).comp t harg).div_const ((2:ℝ)^k)
  convert! hh using 1
  unfold auxiliaryTJet
  rw [pow_succ]
  ring

lemma auxiliaryTJet_eight_lower (q t : ℝ) (hq : 0 ≤ q)
    (ht : t ∈ Set.Ico (-1:ℝ) 1) : 45/16 ≤ auxiliaryTJet q 8 t := by
  have h := auxiliaryJet_eight_lower q ((1+t)/2) hq ⟨by linarith [ht.1],by linarith [ht.2]⟩
  unfold auxiliaryTJet
  norm_num
  linarith

/-- Ordinary polynomial derivatives evaluated at a point. -/
def polynomialJet (P : Polynomial ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.derivative^[k]) P).eval x

lemma polynomialJet_hasDerivAt (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (polynomialJet P k) (polynomialJet P (k+1) x) x := by
  convert! ((Polynomial.derivative^[k]) P).hasDerivAt x using 1
  simp [polynomialJet,Function.iterate_succ_apply']

/-- Monic degree-eight contact product. -/
def contactOmega (z : Fin 4 → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X-Polynomial.C (z i))^2

lemma contactOmega_monic (z : Fin 4 → ℝ) : (contactOmega z).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _

lemma contactOmega_degree (z : Fin 4 → ℝ) : (contactOmega z).degree=8 := by
  rw [contactOmega,Polynomial.degree_prod_of_monic]
  · norm_num [Polynomial.degree_pow]
  · intro i hi
    exact (Polynomial.monic_X_sub_C _).pow _

lemma monic_top_polynomialJet (P : Polynomial ℝ) (N : ℕ)
    (hP : P.Monic) (hN : P.degree=N) (x : ℝ) : polynomialJet P N x=N.factorial := by
  have hn : P.natDegree=N := Polynomial.natDegree_eq_of_degree_eq_some hN
  have he : (Polynomial.derivative^[N]) P=Polynomial.C (N.factorial:ℝ) := by
    ext k
    rw [Polynomial.coeff_iterate_derivative]
    by_cases hk : k=0
    · subst k
      have hc : P.coeff N=1 := hn ▸ hP.coeff_natDegree
      simp [hc,Nat.descFactorial_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [hk]
  simp [polynomialJet,he]

lemma contactOmega_jet_zero (z : Fin 4 → ℝ) (i : Fin 4) (k : ℕ) (hk : k < 2) :
    polynomialJet (contactOmega z) k (z i)=0 := by
  classical
  have hd : (Polynomial.X-Polynomial.C (z i))^2 ∣ contactOmega z :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨P,hP⟩ := hd
  interval_cases k <;> simp [polynomialJet,hP,Polynomial.derivative_mul,Polynomial.derivative_pow]

lemma contactOmega_eval (z : Fin 4 → ℝ) (t : ℝ) :
    (contactOmega z).eval t=∏ i, (t-z i)^2 := by
  simp only [contactOmega,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]

lemma contactOmega_eval_nonneg (z : Fin 4 → ℝ) (t : ℝ) : 0 ≤ (contactOmega z).eval t := by
  rw [contactOmega_eval]
  exact Finset.prod_nonneg (fun i _ => sq_nonneg _)

lemma contactOmega_eval_pos (z : Fin 4 → ℝ) (t : ℝ) (hne : ∀ i, t ≠ z i) :
    0 < (contactOmega z).eval t := by
  rw [contactOmega_eval]
  exact Finset.prod_pos (fun i _ => sq_pos_of_ne_zero (sub_ne_zero.mpr (hne i)))

def doubleContactMultiset (z : Fin 4 → ℝ) : Multiset ℝ :=
  ∑ i, Multiset.replicate 2 (z i)

lemma doubleContactMultiset_card (z : Fin 4 → ℝ) : (doubleContactMultiset z).card=8 := by
  simp [doubleContactMultiset,Multiset.card_sum]

lemma doubleContactMultiset_mem (z : Fin 4 → ℝ) (x : ℝ) :
    x ∈ doubleContactMultiset z ↔ ∃ i, x=z i := by
  simp [doubleContactMultiset,Multiset.mem_sum]

lemma doubleContactMultiset_count (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (doubleContactMultiset z).count (z i)=2 := by
  classical
  change Multiset.count (z i) ((Finset.univ.val.map
    (fun j => Multiset.replicate 2 (z j))).sum)=_
  rw [Multiset.count_sum]
  simp only [Multiset.count_replicate,hz.eq_iff]
  fin_cases i <;> decide

/-- A supplied degree-seven polynomial matching the four values and slopes
has the exact eighth-derivative remainder. -/
theorem hermiteSeven_remainder (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (z : Fin 4 → ℝ) (hz : Function.Injective z) (u : ℝ) (hu : u < 1)
    (hzm : ∀ i, z i ∈ Set.Icc (-1:ℝ) u) (H : Polynomial ℝ) (hH : H.degree < 8)
    (hmatch : ∀ i, ∀ k < 2, polynomialJet H k (z i)=auxiliaryTJet q k (z i))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) u) (hne : ∀ i, t ≠ z i) :
    ∃ ξ ∈ Set.Icc (-1:ℝ) u,
      auxiliaryT q t-H.eval t=auxiliaryTJet q 8 ξ*(contactOmega z).eval t/40320 := by
  classical
  let O := contactOmega z
  let K := (auxiliaryT q t-H.eval t)/O.eval t
  let f : ℕ → ℝ → ℝ := fun k x =>
    auxiliaryTJet q k x-polynomialJet H k x-K*polynomialJet O k x
  have hder (k : ℕ) (x : ℝ) (hx : x < 1) : HasDerivAt (f k) (f (k+1) x) x :=
    ((auxiliaryTJet_hasDerivAt q x hq hx k).sub (polynomialJet_hasDerivAt H k x)).sub
      ((polynomialJet_hasDerivAt O k x).const_mul K)
  have htower : DerivativeTowerOn f 8 (-1) u := by
    constructor
    · intro k hk x hx
      exact (hder k x (hx.2.trans_lt hu)).continuousAt.continuousWithinAt
    · intro k hk x hx
      exact hder k x (hx.2.trans hu)
  have hO : O.eval t ≠ 0 := (contactOmega_eval_pos z t hne).ne'
  have hft : f 0 t=0 := by
    simp only [f,auxiliaryTJet,auxiliaryJet,pow_zero,div_one,polynomialJet,Function.iterate_zero_apply]
    change auxiliaryT q t-H.eval t-K*O.eval t=0
    rw [show K*O.eval t=auxiliaryT q t-H.eval t from div_mul_cancel₀ _ hO]
    ring
  have hfn (i : Fin 4) (k : ℕ) (hk : k < 2) : f k (z i)=0 := by
    dsimp [f,O]
    rw [hmatch i k hk,contactOmega_jet_zero z i k hk]
    ring
  let Z := t ::ₘ doubleContactMultiset z
  have hcard : Z.card=8+1 := by simp [Z,doubleContactMultiset_card]
  have hmem : ∀ x ∈ Z, x ∈ Set.Icc (-1) u := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ht
    · obtain ⟨i,rfl⟩ := (doubleContactMultiset_mem z x).mp hx
      exact hzm i
  have hjet : ∀ x ∈ Z, ∀ k < Z.count x, f k x=0 := by
    intro x hx k hk
    by_cases hxt : x=t
    · subst x
      have hn : t ∉ doubleContactMultiset z := by
        intro hn
        obtain ⟨i,he⟩ := (doubleContactMultiset_mem z t).mp hn
        exact hne i he
      have hk0 : k=0 := by simpa [Z,Multiset.count_eq_zero.mpr hn] using hk
      simpa [hk0] using hft
    · have hn : x ∈ doubleContactMultiset z := (Multiset.mem_cons.mp hx).resolve_left hxt
      obtain ⟨i,rfl⟩ := (doubleContactMultiset_mem z x).mp hn
      have hki : k < 2 := by
        simpa [Z,Multiset.count_cons,hxt,doubleContactMultiset_count z hz i] using hk
      exact hfn i k hki
  obtain ⟨ξ,hξ,hf⟩ := rolle_multiset 8 f (-1) u htower Z hcard hmem hjet
  have hHzero : polynomialJet H 8 ξ=0 := by
    simp only [polynomialJet,Polynomial.iterate_derivative_eq_zero_of_degree_lt hH,
      Polynomial.eval_zero]
  have hOtop : polynomialJet O 8 ξ=40320 := by
    have hh := monic_top_polynomialJet _ 8 (contactOmega_monic z) (contactOmega_degree z) ξ
    norm_num at hh
    exact hh
  change auxiliaryTJet q 8 ξ-polynomialJet H 8 ξ-K*polynomialJet O 8 ξ=0 at hf
  rw [hHzero,hOtop] at hf
  have hK : K=auxiliaryTJet q 8 ξ/40320 := by linarith
  refine ⟨ξ,hξ,?_⟩
  calc
    _ = K*O.eval t := (div_mul_cancel₀ _ hO).symm
    _ = _ := by rw [hK]; ring

/-- Uniform quantitative minorant gap on any compact interval below one. -/
theorem hermiteSeven_gap_on (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (z : Fin 4 → ℝ) (hz : Function.Injective z) (u : ℝ) (hu : u < 1)
    (hzm : ∀ i, z i ∈ Set.Icc (-1:ℝ) u) (H : Polynomial ℝ) (hH : H.degree < 8)
    (hmatch : ∀ i, ∀ k < 2, polynomialJet H k (z i)=auxiliaryTJet q k (z i))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) u) :
    (∏ i, (t-z i)^2)/14336 ≤ auxiliaryT q t-H.eval t := by
  by_cases hnode : ∃ i, t=z i
  · obtain ⟨i,rfl⟩ := hnode
    have hv := hmatch i 0 (by norm_num)
    have ho := contactOmega_jet_zero z i 0 (by norm_num)
    change (contactOmega z).eval (z i)=0 at ho
    have he : ∏ j, (z i-z j)^2=0 := by rwa [contactOmega_eval] at ho
    have hv' : H.eval (z i)=auxiliaryT q (z i) := by
      simpa [polynomialJet,auxiliaryTJet,auxiliaryJet,auxiliaryT] using hv
    rw [he,hv']
    norm_num
  · have hne : ∀ i, t ≠ z i := fun i he => hnode ⟨i,he⟩
    obtain ⟨ξ,hξ,he⟩ := hermiteSeven_remainder q hq z hz u hu hzm H hH hmatch t ht hne
    have hj := auxiliaryTJet_eight_lower q ξ hq.1.le ⟨hξ.1,hξ.2.trans_lt hu⟩
    have ho := contactOmega_eval_nonneg z t
    have hp := mul_le_mul_of_nonneg_right hj ho
    rw [he,← contactOmega_eval]
    nlinarith

/-- Equality holds exactly at the four contacts; the endpoint -1 is not
added unless it was explicitly one of those contacts. -/
theorem hermiteSeven_equality_on (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (z : Fin 4 → ℝ) (hz : Function.Injective z) (u : ℝ) (hu : u < 1)
    (hzm : ∀ i, z i ∈ Set.Icc (-1:ℝ) u) (H : Polynomial ℝ) (hH : H.degree < 8)
    (hmatch : ∀ i, ∀ k < 2, polynomialJet H k (z i)=auxiliaryTJet q k (z i))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) u) :
    H.eval t=auxiliaryT q t ↔ ∃ i, t=z i := by
  constructor
  · intro heq
    by_contra hn
    have hp := contactOmega_eval_pos z t (fun i he => hn ⟨i,he⟩)
    have hg := hermiteSeven_gap_on q hq z hz u hu hzm H hH hmatch t ht
    rw [← contactOmega_eval,heq] at hg
    linarith
  · rintro ⟨i,rfl⟩
    simpa [polynomialJet,auxiliaryTJet,auxiliaryJet,auxiliaryT] using hmatch i 0 (by norm_num)

/-- Full geometric-variable interface: any polynomial of degree at most seven
matching A and its first derivative at four distinct contacts has a uniform
positive gap away from exactly those contacts. No endpoint contact is needed. -/
theorem hermiteSeven_minorant (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (hzm : ∀ i, z i ∈ Set.Ico (-1:ℝ) 1) (H : Polynomial ℝ) (hH : H.degree < 8)
    (hvalue : ∀ i, H.eval (z i)=auxiliaryT q (z i))
    (hslope : ∀ i, H.derivative.eval (z i)=auxSlope q ((1+z i)/2)/2)
    (t : ℝ) (ht : t ∈ Set.Ico (-1:ℝ) 1) :
    H.eval t ≤ auxiliaryT q t ∧
      (∏ i, (t-z i)^2)/14336 ≤ auxiliaryT q t-H.eval t ∧
      (H.eval t=auxiliaryT q t ↔ ∃ i, t=z i) := by
  let u := max t (max (z 0) (max (z 1) (max (z 2) (z 3))))
  have hu : u < 1 := max_lt ht.2
    (max_lt (hzm 0).2 (max_lt (hzm 1).2 (max_lt (hzm 2).2 (hzm 3).2)))
  have hn (i : Fin 4) : z i ∈ Set.Icc (-1:ℝ) u := by
    refine ⟨(hzm i).1,?_⟩
    fin_cases i <;> dsimp [u] <;> order
  have ht' : t ∈ Set.Icc (-1:ℝ) u := ⟨ht.1,le_max_left _ _⟩
  have hmatch (i : Fin 4) (k : ℕ) (hk : k < 2) :
      polynomialJet H k (z i)=auxiliaryTJet q k (z i) := by
    interval_cases k
    · simpa [polynomialJet,auxiliaryTJet,auxiliaryJet,auxiliaryT] using hvalue i
    · simpa [polynomialJet,auxiliaryTJet,auxiliaryJet] using hslope i
  have hg := hermiteSeven_gap_on q hq z hz u hu hn H hH hmatch t ht'
  have he := hermiteSeven_equality_on q hq z hz u hu hn H hH hmatch t ht'
  have hp : 0 ≤ ∏ i, (t-z i)^2 := Finset.prod_nonneg (fun i _ => sq_nonneg _)
  exact ⟨by linarith,hg,he⟩

#print axioms auxiliaryTJet_eight_lower
#print axioms hermiteSeven_remainder
#print axioms hermiteSeven_gap_on
#print axioms hermiteSeven_equality_on
#print axioms hermiteSeven_minorant
end ThomsonNegative.Analytic
