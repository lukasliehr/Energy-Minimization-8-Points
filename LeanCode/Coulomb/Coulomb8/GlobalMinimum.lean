import Coulomb8.FullSolution
import Coulomb8.CertificateColumns
import Coulomb8.CertificatePositivity
import Coulomb8.Candidate

namespace Coulomb8

theorem certificate_lower_bound (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    optimalEnergy ≤ hermiteEnergy x := by
  obtain ⟨w,hw,hA⟩ := full_solution
  have hn := certificateValue_total_nonneg w hw x hx
  have hs := distinctSum_energy x (G a)
  have hf : (fun u v t => (H u+H v+H t)/3-G a/28)=certificateValue w := by
    funext u v t
    exact (certificate_identity w hA u v t).symm
  rw [hf] at hs
  change G a ≤ hermiteEnergy x
  linarith

theorem global_minimum (x : Configuration) (hx : Admissible x) :
    optimalEnergy ≤ coulombEnergy x :=
  (certificate_lower_bound x hx.1).trans (hermiteEnergy_le_coulombEnergy x hx)

theorem antiprism_is_global_minimizer (x : Configuration) (hx : Admissible x) :
    coulombEnergy antiprism ≤ coulombEnergy x := by
  rw [antiprism_energy]
  exact global_minimum x hx

end Coulomb8

#print axioms Coulomb8.global_minimum
#print axioms Coulomb8.antiprism_is_global_minimizer
