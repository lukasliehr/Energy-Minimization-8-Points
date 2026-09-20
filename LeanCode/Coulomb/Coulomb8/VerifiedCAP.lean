import Coulomb8.FullSolution
import Coulomb8.CertificateColumns
import Coulomb8.CertificatePositivity

namespace Coulomb8

/-- The concrete simplified certificate, including its exact identity and positivity. -/
theorem verified_CAP : ∃ w : Fin 192 → ℝ,
    (∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) ∧
    (∀ u v t : ℝ, certificateValue w u v t=(H u+H v+H t)/3-G a/28) ∧
    (∀ x : Configuration, (∀ i, ‖x i‖=1) →
      0 ≤ Thomson8.distinctSum (Thomson8.onTriples x (certificateValue w))) := by
  obtain ⟨w,hw,hA⟩ := full_solution
  exact ⟨w,hw,certificate_identity w hA,certificateValue_total_nonneg w hw⟩

end Coulomb8

#print axioms Coulomb8.verified_CAP
