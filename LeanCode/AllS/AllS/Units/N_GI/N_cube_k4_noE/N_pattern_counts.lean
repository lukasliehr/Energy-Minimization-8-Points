import AllS.Units.N_GI.N_cube_k4_noE.N_s_components
import AllS.Units.N_GI.N_cube_k4_noE.N_face_count

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem shared_pattern_degree (S : SimpleGraph (Fin 8)) (d : Fin 8 → ℕ) (p : Fin 4)
    (v : Fin 4 → Fin 8) (hinj : Function.Injective v)
    (hfull : ∀z,d z=4 ↔ ∃i,v i=z) (hends : ∀a b,S.Adj a b → d a=4 ∧ d b=4)
    (hpat : ∀i j,S.Adj (v i) (v j) ↔ fourGraphAdj (fourPatternBits p) i j) (i : Fin 4) :
    S.degree (v i)=fourGraphDegree (fourPatternBits p) i := by
  have heq : S.neighborFinset (v i)=(Finset.univ.filter (fourGraphAdj (fourPatternBits p) i)).image v := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      have hadj := (S.mem_neighborFinset _ _).mp hz
      obtain ⟨j,rfl⟩ := (hfull z).mp (hends _ _ hadj).2
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hpat i j).mp hadj⟩,rfl⟩
    · intro hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact (S.mem_neighborFinset _ _).mpr ((hpat i j).mpr (Finset.mem_filter.mp hj).2)
  rw [←S.card_neighborFinset_eq_degree,heq,Finset.card_image_of_injective _ hinj]

theorem fourPattern_degrees : ∀p i : Fin 4,fourGraphDegree (fourPatternBits p) i=
    (![![1,2,1,0],![1,2,2,1],![2,2,2,0],![2,2,2,2]] : Fin 4 → Fin 4 → ℕ) p i := by
  decide +kernel

theorem four_labels_deficiency (d t : Fin 8 → ℕ) (v : Fin 4 → Fin 8)
    (hinj : Function.Injective v) (hfull : ∀z,d z=4 ↔ ∃i,v i=z) :
    (∑z : Fin 8,if d z=4 then 3-t z else 0)=∑i : Fin 4,(3-t (v i)) := by
  have hset : Finset.univ.filter (fun z => d z=4)=Finset.univ.image v := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    exact hfull z
  rw [←Finset.sum_filter,hset,Finset.sum_image (fun a _ b _ hab => hinj hab)]

theorem high_unused_count (d t : Fin 8 → ℕ)
    (ht : ∀z,d z=3 → t z≤1) (hk : (Finset.univ.filter (fun z => d z=3)).card=4) :
    (Finset.univ.filter (fun z => d z=3 ∧ t z=1)).card+
      (Finset.univ.filter (fun z => d z=3 ∧ t z=0)).card=4 := by
  have he (z : Fin 8) : (if d z=3 ∧ t z=1 then 1 else 0)+(if d z=3 ∧ t z=0 then 1 else 0)=
      (if d z=3 then (1:ℕ) else 0) := by
    by_cases hd : d z=3
    · have hb := ht z hd
      interval_cases htz : t z <;> simp [hd,htz]
    · simp [hd]
  have hh := congrArg (fun f : Fin 8 → ℕ => ∑z,f z) (funext he)
  simp only [Finset.sum_add_distrib] at hh
  simpa only [Finset.card_filter] using hh.trans (by simpa only [Finset.card_filter] using hk)

#print axioms shared_pattern_degree
#print axioms fourPattern_degrees
#print axioms four_labels_deficiency
#print axioms high_unused_count
end Blueprint.Thomson.Tail.Implementation
