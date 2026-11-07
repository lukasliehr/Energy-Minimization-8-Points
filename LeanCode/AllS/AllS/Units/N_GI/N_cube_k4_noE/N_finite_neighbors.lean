import AllS.Units.N_GI.N_cube_k4_noE.N_triangle_thirds

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem graph_neighbors_exhaust (G : SimpleGraph (Fin 8)) (v : Fin 8) (n : ℕ)
    (f : Fin n → Fin 8) (hf : Function.Injective f) (hd : G.degree v=n)
    (hcontact : ∀i,G.Adj v (f i)) (z : Fin 8) (hz : G.Adj v z) : ∃i,f i=z := by
  have hsub : Finset.univ.image f⊆G.neighborFinset v := by
    rintro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact (G.mem_neighborFinset _ _).mpr (hcontact i)
  have heq : Finset.univ.image f=G.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [G.card_neighborFinset_eq_degree,hd,Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin]
  have hm : z∈Finset.univ.image f := heq.symm ▸ (G.mem_neighborFinset _ _).mpr hz
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  exact ⟨i,hi⟩

theorem no_four_six_inner_products (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i,‖Y i‖=1) (hc : 0≤c) (hcupper : c<3/10)
    (a b d e : Fin 8)
    (hab : inner ℝ (Y a) (Y b)=c) (had : inner ℝ (Y a) (Y d)=c)
    (hae : inner ℝ (Y a) (Y e)=c) (hbd : inner ℝ (Y b) (Y d)=c)
    (hbe : inner ℝ (Y b) (Y e)=c) (hde : inner ℝ (Y d) (Y e)=c) : False := by
  apply no_four_contact_clique_of_card (by simp) (fun i : Fin 4 => Y (![a,b,d,e] i)) c
    (fun i => hY _) hc (by linarith)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Fin.ext_iff] at hij
  all_goals dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ]
  all_goals first
    | exact hab | exact had | exact hae | exact hbd | exact hbe | exact hde
    | exact (real_inner_comm _ _).trans hab | exact (real_inner_comm _ _).trans had
    | exact (real_inner_comm _ _).trans hae | exact (real_inner_comm _ _).trans hbd
    | exact (real_inner_comm _ _).trans hbe | exact (real_inner_comm _ _).trans hde

#print axioms graph_neighbors_exhaust
#print axioms no_four_six_inner_products
end Blueprint.Thomson.Tail.Implementation
