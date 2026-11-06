import AllS.Units.N_FI.N_hermite.N_omega_sign
import AllS.Units.N_F.N_rolle_multiset

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def hermiteNodeMultiset (a : ℝ) (m : Fin 5 → ℕ) : Multiset ℝ :=
  ∑ i, Multiset.replicate (m i) (canonicalNodes a i)

theorem hermiteNodeMultiset_card (a : ℝ) (m : Fin 5 → ℕ) :
    (hermiteNodeMultiset a m).card = ∑ i, m i := by
  simp [hermiteNodeMultiset,Multiset.card_sum]

theorem hermiteNodeMultiset_mem (a x : ℝ) (m : Fin 5 → ℕ) :
    x ∈ hermiteNodeMultiset a m ↔ ∃ i, 0 < m i ∧ x=canonicalNodes a i := by
  simp [hermiteNodeMultiset,Multiset.mem_sum,Multiset.mem_replicate,Nat.pos_iff_ne_zero]

theorem hermiteNodeMultiset_count (a x : ℝ) (m : Fin 5 → ℕ) :
    (hermiteNodeMultiset a m).count x = ∑ i, if canonicalNodes a i=x then m i else 0 := by
  classical
  change Multiset.count x ((Finset.univ.val.map
    (fun i => Multiset.replicate (m i) (canonicalNodes a i))).sum) = _
  rw [Multiset.count_sum]
  simp only [Multiset.count_replicate]
  rfl

theorem hermiteNodeMultiset_count_node (a : ℝ) (m : Fin 5 → ℕ) (ha : physical a)
    (i : Fin 5) : (hermiteNodeMultiset a m).count (canonicalNodes a i)=m i := by
  classical
  rw [hermiteNodeMultiset_count]
  simp only [(canonicalNodes_strictMono a ha).injective.eq_iff]
  simp

theorem polynomialJets_hasDerivAt (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (polynomialJets P k) (polynomialJets P (k+1) x) x := by
  convert! ((Polynomial.derivative^[k]) P).hasDerivAt x using 1 <;>
    simp [polynomialJets,Function.iterate_succ_apply']

theorem hermite_remainder (s a t : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m)
    (ht : -1 ≤ t ∧ t < 1) (hne : ∀ i, 0 < m i → t ≠ canonicalNodes a i) :
    ∃ ξ, -1 ≤ ξ ∧ ξ < 1 ∧
      phi s t-(hermitePolynomial s a m).eval t =
        potentialJet s (∑ i,m i) ξ * (hermiteOmega a m).eval t / (∑ i,m i).factorial := by
  classical
  let N := ∑ i,m i
  let H := hermitePolynomial s a m
  let O := hermiteOmega a m
  let K := (phi s t-H.eval t)/O.eval t
  let f : ℕ → ℝ → ℝ := fun k x =>
    potentialJet s k x-polynomialJets H k x-K*polynomialJets O k x
  let u := max t (canonicalNodes a 4)
  have hu : u < 1 := max_lt ht.2 (canonicalNodes_bounds a ha 4).2
  have hnode (i : Fin 5) : canonicalNodes a i ∈ Set.Icc (-1) u := by
    refine ⟨(canonicalNodes_bounds a ha i).1,?_⟩
    exact ((canonicalNodes_strictMono a ha).monotone (Fin.le_last i)).trans (le_max_right _ _)
  have htmem : t ∈ Set.Icc (-1) u := ⟨ht.1,le_max_left _ _⟩
  have hder (k : ℕ) (x : ℝ) (hx : x < 1) : HasDerivAt (f k) (f (k+1) x) x :=
    ((potential_jets_tower s x k hs hx).1.sub (polynomialJets_hasDerivAt H k x)).sub
      ((polynomialJets_hasDerivAt O k x).const_mul K)
  have htower : DerivativeTowerOn f N (-1) u := by
    constructor
    · intro k hk x hx
      exact (hder k x (lt_of_le_of_lt hx.2 hu)).continuousAt.continuousWithinAt
    · intro k hk x hx
      exact hder k x (hx.2.trans hu)
  have hO : O.eval t ≠ 0 := (hermite_omega_sign a t D m ha hm ht hne).1.ne'
  have hft : f 0 t=0 := by
    change phi s t-H.eval t-K*O.eval t=0
    rw [show K*O.eval t=phi s t-H.eval t from div_mul_cancel₀ _ hO]
    ring
  have hfn (i : Fin 5) (k : ℕ) (hk : k < m i) : f k (canonicalNodes a i)=0 := by
    dsimp [f,H,O]
    rw [hermitePolynomial_jets s a m ha i k hk,hermiteOmega_jets_zero a m i k hk]
    ring
  let Z := t ::ₘ hermiteNodeMultiset a m
  have hcard : Z.card=N+1 := by simp [Z,N,hermiteNodeMultiset_card]
  have hmem : ∀ x ∈ Z, x ∈ Set.Icc (-1) u := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact htmem
    · obtain ⟨i,hi,rfl⟩ := (hermiteNodeMultiset_mem a x m).mp hx
      exact hnode i
  have hjet : ∀ x ∈ Z, ∀ k < Z.count x, f k x=0 := by
    intro x hx k hk
    by_cases hxt : x=t
    · subst x
      have hn : t ∉ hermiteNodeMultiset a m := by
        intro hn
        obtain ⟨i,hi,he⟩ := (hermiteNodeMultiset_mem a t m).mp hn
        exact hne i hi he
      have hk0 : k=0 := by simpa [Z,Multiset.count_eq_zero.mpr hn] using hk
      simpa [hk0] using hft
    · have hn : x ∈ hermiteNodeMultiset a m := (Multiset.mem_cons.mp hx).resolve_left hxt
      obtain ⟨i,hi,rfl⟩ := (hermiteNodeMultiset_mem a x m).mp hn
      have hki : k < m i := by
        simpa [Z,Multiset.count_cons,hxt,hermiteNodeMultiset_count_node a m ha i] using hk
      exact hfn i k hki
  obtain ⟨ξ,hξ,hf⟩ := rolle_multiset N f (-1) u htower Z hcard hmem hjet
  refine ⟨ξ,hξ.1,hξ.2.trans_lt hu,?_⟩
  have hH : polynomialJets H N ξ=0 := by
    change polynomialJets (hermitePolynomial s a m) (∑ i,m i) ξ=0
    simp only [polynomialJets,Polynomial.iterate_derivative_eq_zero_of_degree_lt
      (hermitePolynomial_degree s a m),Polynomial.eval_zero]
  have hON : polynomialJets O N ξ=N.factorial := hermiteOmega_jet_top a m ξ
  change potentialJet s N ξ-polynomialJets H N ξ-K*polynomialJets O N ξ=0 at hf
  rw [hH,hON] at hf
  have hfac : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hK : K=potentialJet s N ξ/N.factorial := by apply (eq_div_iff hfac).mpr; linarith
  change phi s t-H.eval t=potentialJet s N ξ*O.eval t/N.factorial
  calc
    _ = K*O.eval t := (div_mul_cancel₀ _ hO).symm
    _ = _ := by rw [hK]; ring

#check hermite_remainder
#print axioms hermite_remainder
end Blueprint.Thomson.Finite
