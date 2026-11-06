import AllS.Units.N_GI.N_contact_weights.N_log_error

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_weights_assemble (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) :
    contactScaledLinear p q e<119/100 ∧
    -Real.log (tailCstar p)<contactScaledLinear p q e ∧
    |(p/tau)*contactDelta q e.1 (contactNext e)|<3 ∧
    (7:ℝ)/25<(tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+2) ∧
    |p*Real.log (squaredDistance (orthographicChart q) e.1 (contactNext e)/tau)-contactScaledLinear p q e|<3/25 :=
  ⟨contact_weights_linear_upper p hp q hq e,(contact_weights_linear_lower p hp q hq e).1,
    (contact_weights_linear_lower p hp q hq e).2,contact_weights_hessian_weight p hp q hq e,
    contact_weights_log_error p hp q hq e⟩

#print axioms contact_weights_assemble
end Blueprint.Thomson.Tail.Implementation
