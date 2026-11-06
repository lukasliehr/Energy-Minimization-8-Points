import AllS.Units.N_GI.N_variance_sharp.N_quartic_bridge
import AllS.Units.N_GI.N_centered_quadratic.N_contact_operator
import AllS.Units.N_GI.N_cubic_absorption.N_square_completion

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Polarization of the actual cubic variance cross term. -/
def varianceTrilinear (q v z : TangentCoordinates) : ℝ :=
  (2/3:ℝ)*∑ e : ContactIndex, contactWeight e *
    (contactLinearArray q e * inner ℝ v (contactM e z) +
     contactLinearArray v e * inner ℝ q (contactM e z) +
     contactLinearArray z e * inner ℝ q (contactM e v))

theorem varianceTrilinear_diagonal (q : TangentCoordinates) :
    varianceTrilinear q q q = varianceCubic q := by
  unfold varianceTrilinear varianceCubic
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [contactM_quadratic]
  simp only [contactQuadraticArray]
  ring

theorem varianceTrilinear_swap12 (q v z : TangentCoordinates) :
    varianceTrilinear q v z=varianceTrilinear v q z := by
  unfold varianceTrilinear
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [contactM_symmetric e q v]
  ring

theorem varianceTrilinear_swap23 (q v z : TangentCoordinates) :
    varianceTrilinear q v z=varianceTrilinear q z v := by
  unfold varianceTrilinear
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [contactM_symmetric e v z]
  ring

/-- The tensor certificate can use any physical quadratic absorption map on
the rotation slice. Only its exact contraction and norm bound remain to check. -/
theorem variance_absorption_of_physical_square
    (A : rotationSlice →ₗ[ℝ] rotationSlice)
    (hquad : ∀ q : rotationSlice, inner ℝ q (A q) =
      (∑ e : ContactIndex, contactWeight e*(contactLinearArray q e)^2)-
        (17:ℝ)/5*‖q‖^2)
    (hsym : ∀ q v : rotationSlice, inner ℝ q (A v)=inner ℝ v (A q))
    (U : rotationSlice → rotationSlice)
    (hcontract : ∀ q : rotationSlice,
      inner ℝ q (A (U q))=varianceTrilinear q q q)
    (hbound : ∀ q : rotationSlice, inner ℝ (U q) (A (U q)) ≤ 15*‖q‖^4) :
    VarianceCubicAbsorption := by
  have hpos (q : rotationSlice) : 0 ≤ inner ℝ q (A q) := by
    rw [hquad]
    have h := contact_spectrum_physical_weighted q q.property
    change (59546/15625)*‖q‖^2 ≤
      ∑ e : ContactIndex, contactWeight e*(contactLinearArray q e)^2 at h
    nlinarith [sq_nonneg ‖q‖]
  intro q hq
  let v : rotationSlice := ⟨q,hq⟩
  have hc : inner ℝ v (A (U v))=varianceCubic q :=
    (hcontract v).trans (varianceTrilinear_diagonal q)
  have hh := (cubic_square_completion A hpos hsym v (U v)
    (varianceCubic q) (15*‖v‖^4) hc (hbound v)).2
  rw [hquad] at hh
  convert! hh using 1 <;> dsimp [v] <;> ring

#print axioms varianceTrilinear_diagonal
#print axioms variance_absorption_of_physical_square

/-- A positive extension to the ambient space avoids a separate range proof
for the quadratic absorption map. The physical identities are needed only on V. -/
theorem variance_absorption_of_full_space_square
    (A : TangentCoordinates →ₗ[ℝ] TangentCoordinates)
    (hpos : ∀ q, 0 ≤ inner ℝ q (A q))
    (hsym : ∀ q v, inner ℝ q (A v)=inner ℝ v (A q))
    (hquad : ∀ q : TangentCoordinates, q∈rotationSlice → inner ℝ q (A q) =
      (∑ e : ContactIndex, contactWeight e*(contactLinearArray q e)^2)-
        (17:ℝ)/5*‖q‖^2)
    (U : TangentCoordinates → TangentCoordinates)
    (hcontract : ∀ q : TangentCoordinates, q∈rotationSlice →
      inner ℝ q (A (U q))=varianceTrilinear q q q)
    (hbound : ∀ q : TangentCoordinates, q∈rotationSlice →
      inner ℝ (U q) (A (U q)) ≤ 15*‖q‖^4) : VarianceCubicAbsorption := by
  intro q hq
  have hc := (hcontract q hq).trans (varianceTrilinear_diagonal q)
  have hh := (cubic_square_completion A hpos hsym q (U q)
    (varianceCubic q) (15*‖q‖^4) hc (hbound q hq)).2
  rw [hquad q hq] at hh
  convert! hh using 1 <;> ring

#print axioms variance_absorption_of_full_space_square
end Blueprint.Thomson.Tail.Implementation
