import AllS.Units.N_FI.N_raw_projection.N_parity_formula
import AllS.Units.N_FI.N_raw_projection.N_sign_standard
import AllS.Units.N_FI.N_raw_projection.N_target_directions
import AllS.Units.N_FI.N_kernels.N_finite_layout_linkage

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

theorem reynolds_six (p : Poly3) : reynolds p = (6 : ℝ)⁻¹ •
    (p + MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) p +
      MvPolynomial.rename (Equiv.swap (0 : Fin 3) 2) p +
      MvPolynomial.rename (Equiv.swap (1 : Fin 3) 2) p +
      MvPolynomial.rename ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) p +
      MvPolynomial.rename ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)) p) := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 3)))=
      {Equiv.refl _,Equiv.swap 0 1,Equiv.swap 0 2,Equiv.swap 1 2,
        (Equiv.swap 0 1).trans (Equiv.swap 1 2),(Equiv.swap 1 2).trans (Equiv.swap 0 1)} := by
    decide
  simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.coe_sum,Finset.sum_apply,AlgHom.toLinearMap_apply,hp]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  congr 1
  simp only [Equiv.coe_refl,MvPolynomial.rename_id_apply]
  abel

def sparseInvariantPolynomial (p : RawCatalogue.SparsePoly) : Poly3 :=
  invariantSubst (RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial p))

theorem sparseInvariantPolynomial_nil : sparseInvariantPolynomial []=0 := by
  simp [sparseInvariantPolynomial,RawCatalogue.sparsePolynomial]

theorem sparseInvariantPolynomial_cons (t : Tag) (c : ℚ) (p : RawCatalogue.SparsePoly) :
    sparseInvariantPolynomial ((t,c)::p)=
      MvPolynomial.C (c:ℝ)*invariantMonomial t+sparseInvariantPolynomial p := by
  simp [sparseInvariantPolynomial,RawCatalogue.sparsePolynomial,RawCatalogue.ratToReal,
    invariantSubst,invariantMonomial,mul_assoc]

@[simp] theorem repeatSubst_X (x y : Fin 3) :
    repeatSubst x (MvPolynomial.X y)=![MvPolynomial.X x,MvPolynomial.X x,1] y := by
  simp [repeatSubst]

@[simp] theorem repeatSubst_C (x : Fin 3) (c : ℝ) :
    repeatSubst x (MvPolynomial.C c)=MvPolynomial.C c := by
  simp [repeatSubst]

#print axioms reynolds_six
#print axioms sparseInvariantPolynomial_cons
end Blueprint.Thomson.Finite
