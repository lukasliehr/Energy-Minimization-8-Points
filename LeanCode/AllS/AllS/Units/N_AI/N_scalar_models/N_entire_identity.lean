import AllS.Units.N_AI.N_scalar_models.N_entire_remainder
import Blueprint.FiniteDefinitions

noncomputable section
namespace Blueprint.CAP

def rieszLogCoordinate (t : ℝ) : ℝ := -(Real.log (2-2*t))/2

def ScalarEntireIdentityStatement : Prop :=
  ∀ (s t : ℝ), 0 ≤ s → t < 1 →
    rieszLogCoordinate t*entirePsi (s*rieszLogCoordinate t) = Blueprint.Thomson.Finite.phi s t

theorem entirePsi_zero : entirePsi 0=1 := by simp [entirePsi]

theorem mul_entirePsi (z : ℝ) : z*entirePsi z=Real.exp z-1 := by
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => Real.exp (v*z))
      (z*Real.exp (u*z)) u := by
    simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id u).mul_const z).exp
  calc
    z*entirePsi z = ∫ u in (0:ℝ)..1, z*Real.exp (u*z) :=
      (intervalIntegral.integral_const_mul z _).symm
    _ = Real.exp (1*z)-Real.exp (0*z) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _=>hd u)
        ((by fun_prop : Continuous (fun u : ℝ => z*Real.exp (u*z))).intervalIntegrable 0 1)
    _ = Real.exp z-1 := by simp

theorem scalar_models_entire_identity : ScalarEntireIdentityStatement := by
  intro s t _ ht
  have hd : 0<2-2*t := by linarith
  by_cases hs : s=0
  · subst s
    simp only [zero_mul, entirePsi_zero, mul_one, Blueprint.Thomson.Finite.phi, if_pos rfl]
    dsimp [rieszLogCoordinate]
    ring
  · rw [Blueprint.Thomson.Finite.phi, if_neg hs]
    apply (eq_div_iff hs).mpr
    have hexp : Real.exp (s*rieszLogCoordinate t)=(2-2*t)^(-s/2) := by
      rw [Real.rpow_def_of_pos hd]
      congr 1
      dsimp [rieszLogCoordinate]
      ring
    calc
      rieszLogCoordinate t*entirePsi (s*rieszLogCoordinate t)*s =
          (s*rieszLogCoordinate t)*entirePsi (s*rieszLogCoordinate t) := by ring
      _ = Real.exp (s*rieszLogCoordinate t)-1 := mul_entirePsi _
      _ = (2-2*t)^(-s/2)-1 := by rw [hexp]

#check scalar_models_entire_identity
#print ScalarEntireIdentityStatement
#print axioms scalar_models_entire_identity
#print axioms mul_entirePsi
end Blueprint.CAP
