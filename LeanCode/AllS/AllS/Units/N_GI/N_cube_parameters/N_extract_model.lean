import AllS.Units.N_GI.N_cube_parameters.N_all_pairs

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_extract_model (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hAA : ∀i j,i≠j → inner ℝ (A i) (A j)≤c)
    (hBB : ∀i j,i≠j → inner ℝ (B i) (B j)≤c)
    (hAB : ∀i j,inner ℝ (A i) (B j)≤c) :
    ∃ (e : Fin 3 → Point) (q : Fin 3 → ℝ),Orthonormal ℝ e ∧ CubeFeasible c q ∧
      (∀i,A i=cubeModelA e q i) ∧ (∀i,B i=cubeModelB e c q i) := by
  obtain ⟨e,x,he,hx,hA,hB,hs,hr⟩ := disphenoid_coordinates A B c hc hAunit hBunit hAinj hBinj hcross (fun i => hAB i i)
  let q : Fin 3 → ℝ := fun k => (x k)^2
  have hq : ∀k,0<q k := fun k => sq_pos_of_pos (hx k)
  have hroot : ∀k,Real.sqrt (q k)=x k := fun k => Real.sqrt_sq (hx k).le
  have hEq : CubeEquations c q := ⟨hc,hq,hs,hr⟩
  have hAm : ∀i,A i=cubeModelA e q i := by intro i;simpa only [cubeModelA,hroot] using hA i
  have hBm : ∀i,B i=cubeModelB e c q i := by intro i;simpa only [cubeModelB,hroot] using hB i
  have hbound : CubeModelInnerBound e c q := by
    constructor
    · intro i j hij;rw [←hAm i,←hAm j];exact hAA i j hij
    constructor
    · intro i j hij;rw [←hBm i,←hBm j];exact hBB i j hij
    · intro i j;rw [←hAm i,←hBm j];exact hAB i j
  exact ⟨e,q,he,(cube_parameters_all_pairs e he c q hEq).1.mp hbound,hAm,hBm⟩

#print axioms cube_extract_model
end Blueprint.Thomson.Tail.Implementation
