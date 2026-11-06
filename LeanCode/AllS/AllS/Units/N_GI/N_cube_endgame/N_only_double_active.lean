import AllS.Units.N_GI.N_cube_endgame.N_local_descent
import AllS.Units.N_G.N_spanning_cube

noncomputable section
open Real SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_extract_configuration (Y : Fin 8 → Point) (hY : Blueprint.Thomson.IsConfiguration Y)
    (c : ℝ) (hc : 0<c) (hb : PackingInnerBound c Y) (hspan : HasSpanningCube (actualContactGraph Y c)) :
    ∃(e : Fin 3 → Point)(label : CubeVertex ≃ Fin 8)(q : Fin 3 → ℝ),
      Orthonormal ℝ e ∧ CubeFeasible c q ∧ Y=cubeConfiguration e label c q := by
  obtain ⟨label,hlabel⟩ := hspan
  let A : Fin 4 → Point := fun i => Y (label (0,i))
  let B : Fin 4 → Point := fun i => Y (label (1,i))
  have hAinj : Function.Injective A := by
    intro i j hij
    exact congrArg Prod.snd (label.injective (hY.2 hij))
  have hBinj : Function.Injective B := by
    intro i j hij
    exact congrArg Prod.snd (label.injective (hY.2 hij))
  have hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c := fun i j hij => (hlabel i j hij).2
  have hAA : ∀i j,i≠j → inner ℝ (A i) (A j)≤c := by
    intro i j hij
    apply hb
    intro he
    exact hij (congrArg Prod.snd (label.injective he))
  have hBB : ∀i j,i≠j → inner ℝ (B i) (B j)≤c := by
    intro i j hij
    apply hb
    intro he
    exact hij (congrArg Prod.snd (label.injective he))
  have hAB : ∀i j,inner ℝ (A i) (B j)≤c := by
    intro i j
    apply hb
    intro he
    have hh := congrArg Prod.fst (label.injective he)
    norm_num at hh
  obtain ⟨e,q,he,hq,hA,hB⟩ := cube_extract_model A B c hc (fun i => hY.1 _) (fun i => hY.1 _)
    hAinj hBinj hcross hAA hBB hAB
  refine ⟨e,label,q,he,hq,?_⟩
  funext i
  obtain ⟨⟨v,j⟩,rfl⟩ := label.surjective i
  fin_cases v
  · simpa [cubeConfiguration,cubeVertexModel,A] using hA j
  · simpa [cubeConfiguration,cubeVertexModel,B] using hB j

theorem cube_endgame_only_double_active (Y : Fin 8 → Point) (hY : Blueprint.Thomson.IsConfiguration Y)
    (c : ℝ) (hmax : packingMaxInner Y=c) (hc : 0<c) (hcub : c<7/25)
    (hspan : HasSpanningCube (actualContactGraph Y c)) (hmin : PackingLocalMinimum Y) :
    c=packingHeight ∧ ∃(e : Fin 3 → Point)(label : CubeVertex ≃ Fin 8)(q : Fin 3 → ℝ),
      Orthonormal ℝ e ∧ CubeFeasible c q ∧ Y=cubeConfiguration e label c q ∧ CubeAntiprismParameters c q := by
  have hb : PackingInnerBound c Y := (packingMaxInner_le_iff Y c).mp hmax.le
  obtain ⟨e,label,q,he,hq,hrepr⟩ := cube_extract_configuration Y hY c hc hb hspan
  have hparam : CubeAntiprismParameters c q := cube_local_minimum_parameters e he label c q hq hcub (hrepr ▸ hmin)
  exact ⟨hparam.1,e,label,q,he,hq,hrepr,hparam⟩

#print axioms cube_endgame_only_double_active
end Blueprint.Thomson.Tail.Implementation
