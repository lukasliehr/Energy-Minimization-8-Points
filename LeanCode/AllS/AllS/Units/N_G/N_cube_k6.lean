import AllS.Units.N_GI.N_cube_k6.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail
open Implementation (degreeThreeVertices TriFace triFaceVertices sharedTriangleGraph graphWithout actualContactGraph CubeVertex)

theorem cube_k6 (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) :
    ∃ f g : TriFace Y c hY hc,∃u v : Fin 8,f≠g ∧ u≠v ∧
      triFaceVertices f∩triFaceVertices g={u,v} ∧
      (∀a b,(sharedTriangleGraph hY hc).Adj a b ↔ (a=u ∧ b=v) ∨ (a=v ∧ b=u)) ∧
      ∃ e : CubeVertex ≃ Fin 8,∀a b : CubeVertex,
        (graphWithout (actualContactGraph Y c) (sharedTriangleGraph hY hc)).Adj (e a) (e b) ↔
          a.1≠b.1 ∧ a.2≠b.2 :=
  Implementation.cube_k6_assemble Y c hY hc hcupper hirr hbound hne hsupport hk

#print axioms cube_k6
end Blueprint.Thomson.Tail
