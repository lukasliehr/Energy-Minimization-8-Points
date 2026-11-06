import AllS.Units.N_F.N_upstream_evaluation

noncomputable section
namespace Blueprint.Thomson.Finite

def MomentCountingContract : Prop := ∀ m k : ℕ, ∀ Y : Configuration,
  (∀ i, ‖Y i‖=1) → ∀ i j : Fin m,
    distinctPolySum Y (kernelRPoly k i.val j.val) = 6*canonicalMoment m k Y i j
theorem counting_moment_identity (m k : ℕ) (Y : Configuration) (hY : ∀ i, ‖Y i‖=1)
    (i j : Fin m) : distinctPolySum Y (kernelRPoly k i.val j.val) =
      6*canonicalMoment m k Y i j := by
  rw [canonicalMoment_eq_generic]
  convert! GenericMoments.sum_Rfun_eq_moment m k Y hY i j using 1
  apply congrArg DistinctSum
  funext r s t
  simp [polyOnTriples,GenericMoments.onTriples,kernelRPoly_eval]

#check counting_moment_identity
#print axioms counting_moment_identity
#check MomentCountingContract
#print axioms MomentCountingContract
end Blueprint.Thomson.Finite
