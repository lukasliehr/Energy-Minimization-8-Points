import AllS.Units.N_GI.N_cube_parameters.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation

theorem cube_parameters (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    (CubeModelInnerBound e c q ↔ CubeFeasible c q) ∧
    (∀i j,i≠j → inner ℝ (cubeModelA e q i) (cubeModelA e q j)=2*q (cubePairAxis i j)-1) ∧
    (∀i j,i≠j → inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)=2*c^2/q (cubePairAxis i j)-1) ∧
    (∀i j,inner ℝ (cubeModelA e q i) (cubeModelB e c q j)=if i=j then -3*c else c) ∧
    (CubeFeasible c q → CubeFeasible c (cubeDual c q) ∧ cubeDual c (cubeDual c q)=q ∧
      (∀k,cubeDual c q k=cubeUpper c ↔ q k=cubeLower c) ∧
      (∀k,cubeDual c q k=cubeLower c ↔ q k=cubeUpper c)) ∧
    (CubeFeasible c q → (∀i j,q i=cubeUpper c → q j=cubeUpper c → i=j) ∧
      (∀i j,q i=cubeLower c → q j=cubeLower c → i=j)) :=
  Implementation.cube_parameters_assemble e he c q h

#print axioms cube_parameters
end Blueprint.Thomson.Tail
