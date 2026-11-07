import AllS.Units.N_GI.N_cube_parameters.N_model_inner
import AllS.Units.N_GI.N_cube_parameters.N_duality

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def CubeModelInnerBound (e : Fin 3 → Point) (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  (∀i j,i≠j → inner ℝ (cubeModelA e q i) (cubeModelA e q j)≤c) ∧
  (∀i j,i≠j → inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)≤c) ∧
  (∀i j,inner ℝ (cubeModelA e q i) (cubeModelB e c q j)≤c)

theorem cubePairAxis_zero_succ (k : Fin 3) : cubePairAxis 0 k.succ=k := by
  fin_cases k <;> rfl

theorem cube_model_bounds_iff (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    CubeModelInnerBound e c q ↔ ∀k,cubeLower c≤q k ∧ q k≤cubeUpper c := by
  obtain ⟨hc,hq,hs,hr⟩ := h
  constructor
  · rintro ⟨hA,hB,_⟩ k
    have ha := hA 0 k.succ (Fin.succ_ne_zero k).symm
    have hb := hB 0 k.succ (Fin.succ_ne_zero k).symm
    rw [cubeModelA_off_diagonal e he q hq hs 0 k.succ (Fin.succ_ne_zero k).symm,
      cubePairAxis_zero_succ] at ha
    rw [cubeModelB_off_diagonal e he c q hq hr 0 k.succ (Fin.succ_ne_zero k).symm,
      cubePairAxis_zero_succ] at hb
    have hu : q k≤cubeUpper c := by unfold cubeUpper;linarith
    have hv : c^2/q k≤cubeUpper c := by
      rw [mul_div_assoc] at hb
      unfold cubeUpper;linarith
    exact ⟨(cube_dual_upper_iff c (q k) hc (hq k)).mp hv,hu⟩
  · intro hbox
    refine ⟨?_,?_,?_⟩
    · intro i j hij
      rw [cubeModelA_off_diagonal e he q hq hs i j hij]
      have hh := (hbox (cubePairAxis i j)).2
      unfold cubeUpper at hh
      linarith
    · intro i j hij
      rw [cubeModelB_off_diagonal e he c q hq hr i j hij]
      have hh := (cube_dual_upper_iff c (q (cubePairAxis i j)) hc (hq _)).mpr (hbox _).1
      unfold cubeUpper at hh
      rw [mul_div_assoc]
      linarith
    · intro i j
      rw [cubeModel_cross_inner e he c q hq]
      split_ifs <;> linarith

theorem cube_parameters_all_pairs (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    (CubeModelInnerBound e c q ↔ CubeFeasible c q) ∧
    (∀i j,i≠j → inner ℝ (cubeModelA e q i) (cubeModelA e q j)=2*q (cubePairAxis i j)-1) ∧
    (∀i j,i≠j → inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)=2*c^2/q (cubePairAxis i j)-1) ∧
    (∀i j,inner ℝ (cubeModelA e q i) (cubeModelB e c q j)=if i=j then -3*c else c) := by
  refine ⟨?_,cubeModelA_off_diagonal e he q h.2.1 h.2.2.1,
    cubeModelB_off_diagonal e he c q h.2.1 h.2.2.2,cubeModel_cross_inner e he c q h.2.1⟩
  rw [cube_model_bounds_iff e he c q h]
  exact ⟨fun hb => ⟨h,hb⟩,fun hh => hh.2⟩

#print axioms cube_parameters_all_pairs
end Blueprint.Thomson.Tail.Implementation
