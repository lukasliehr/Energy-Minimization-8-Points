import AllS.Units.N_FI.N_kernels.RFBridge

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFBridge
open Blueprint.CAP

/-- Literal exported coefficients paired with the actual source raw row order. -/
def rfRawColumn (a : ℝ) (coefficients : List RatFun) (raw : List Poly3) : Poly3 :=
  (coefficients.zipWith (fun r p => MvPolynomial.C (r.eval a)*p) raw).sum

theorem parity_sum_indexed {M : Type*} [AddCommMonoid M] (odd : Bool) (f : Tag → M) :
    (∑ v ∈ (parityPivotTags odd).toFinset,f v)=∑ r : ParityIndex odd,f (parityIndexTag odd r) := by
  classical
  symm
  refine Finset.sum_bij (fun r _=>parityIndexTag odd r) ?_ ?_ ?_ ?_
  · intro r hr
    exact parityIndexTag_mem odd r
  · intro r hr s hs he
    exact parityIndexTag_injective odd he
  · intro t ht
    obtain ⟨r,hr⟩ := (parityTagMap_bijective odd).2 ⟨t,ht⟩
    exact ⟨r,Finset.mem_univ _,congrArg Subtype.val hr⟩
  · intro r hr
    rfl

theorem parity_feature_expansion_indexed (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag) :
    parityKernelFeature odd a t=(if odd then parityOdd else 1)*parityMonomial t-
      ∑ r : ParityIndex odd,
        MvPolynomial.C (parityKernelCoefficients a odd t (parityIndexTag odd r))*
          ((if odd then parityOdd else 1)*parityMonomial (parityIndexTag odd r)) := by
  rw [parityKernelFeature_expansion a ha,parity_sum_indexed]

theorem parity_sum_even {M : Type*} [AddCommMonoid M] (f : ParityIndex false → M) :
    (∑ r,f r)=f ⟨0,⟨0,by decide⟩⟩+f ⟨0,⟨1,by decide⟩⟩+f ⟨0,⟨2,by decide⟩⟩+f ⟨0,⟨3,by decide⟩⟩+
      f ⟨1,⟨0,by decide⟩⟩+f ⟨1,⟨1,by decide⟩⟩+f ⟨1,⟨2,by decide⟩⟩+f ⟨2,⟨0,by decide⟩⟩+f ⟨2,⟨1,by decide⟩⟩+f ⟨2,⟨2,by decide⟩⟩+f ⟨3,⟨0,by decide⟩⟩+f ⟨3,⟨1,by decide⟩⟩ := by
  rw [Fintype.sum_sigma,Fin.sum_univ_four]
  change ((∑ j : Fin 4,f ⟨0,j⟩)+(∑ j : Fin 3,f ⟨1,j⟩)+
    (∑ j : Fin 3,f ⟨2,j⟩)+(∑ j : Fin 2,f ⟨3,j⟩))=_
  rw [Fin.sum_univ_four,Fin.sum_univ_three,Fin.sum_univ_three,Fin.sum_univ_two]
  abel

theorem parity_sum_odd {M : Type*} [AddCommMonoid M] (f : ParityIndex true → M) :
    (∑ r,f r)=f ⟨0,⟨0,by decide⟩⟩+f ⟨0,⟨1,by decide⟩⟩+f ⟨0,⟨2,by decide⟩⟩+
      f ⟨1,⟨0,by decide⟩⟩+f ⟨1,⟨1,by decide⟩⟩+f ⟨1,⟨2,by decide⟩⟩+f ⟨2,⟨0,by decide⟩⟩+f ⟨2,⟨1,by decide⟩⟩+f ⟨3,⟨0,by decide⟩⟩ := by
  rw [Fintype.sum_sigma,Fin.sum_univ_four]
  change ((∑ j : Fin 3,f ⟨0,j⟩)+(∑ j : Fin 3,f ⟨1,j⟩)+
    (∑ j : Fin 2,f ⟨2,j⟩)+(∑ j : Fin 1,f ⟨3,j⟩))=_
  rw [Fin.sum_univ_three,Fin.sum_univ_three,Fin.sum_univ_two,Fin.sum_univ_one]
  abel

end Blueprint.Thomson.Finite.RFBridge
