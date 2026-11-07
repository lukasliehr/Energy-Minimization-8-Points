import Mathlib.Analysis.Real.Sqrt
import ThomsonCompact.TailC.StageSound

/-!
# TailC: the stage as a polynomial identity over `ℝ` (workstream TC1)

`κ : ℤ√2 →+* ℝ` (`√2 ↦ Real.sqrt 2`), `sv l m = Σ_{e ∈ l} κ(e) m(e.i)` (a sparse vector evaluated on monomials
`m`). `stage_real`: if the stage passes and the monomials multiply through the table
(`m i * m j = M (gamD P i j)`), then `sv (stage P ts).2 M = Σ_terms c · sv p m · sv q m`.
-/

namespace ThomsonCompact.TailC
open Finset

/-- `ℤ√2 → ℝ`, `√2 ↦ Real.sqrt 2`. -/
noncomputable def κ : ℤ√2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num⟩

theorem κ_apply (z : ℤ√2) : κ z = z.re + z.im * Real.sqrt 2 := by
  simp [κ]

/-- A sparse vector evaluated on monomials `m`. -/
noncomputable def sv (l : List Ent) (m : ℕ → ℝ) : ℝ := (l.map fun e => κ (ev e) * m e.1).sum

theorem lsum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsum_range f n, Finset.sum_range_succ]; simp

theorem lsum_mul_right {α R : Type*} [Semiring R] (l : List α) (f : α → R) (c : R) :
    (l.map f).sum * c = (l.map fun a => f a * c).sum := (List.sum_map_mul_right l f c).symm

theorem κ_S (gm : ℕ → ℕ → ℕ) (γ : ℕ) (p q : List Ent) :
    κ (p.map fun e => (q.map fun f => if gm e.1 f.1 = γ then ev e * ev f else 0).sum).sum =
      (p.map fun e => (q.map fun f => if gm e.1 f.1 = γ then κ (ev e) * κ (ev f) else 0).sum).sum := by
  rw [map_list_sum, List.map_map]
  refine lsum_congr _ _ _ (fun e _ => ?_)
  simp only [Function.comp, map_list_sum, List.map_map]
  refine lsum_congr _ _ _ (fun f _ => ?_)
  simp only [Function.comp]
  split_ifs <;> simp

theorem inner_collapse (gm : ℕ → ℕ → ℕ) (N : ℕ) (M : ℕ → ℝ) (p q : List Ent)
    (hN : ∀ e ∈ p, ∀ f ∈ q, gm e.1 f.1 < N) :
    ∑ γ ∈ range N, (p.map fun e => (q.map fun f => if gm e.1 f.1 = γ then κ (ev e) * κ (ev f) else 0).sum).sum
        * M γ = (p.map fun e => (q.map fun f => κ (ev e) * κ (ev f) * M (gm e.1 f.1)).sum).sum := by
  have h1 : ∀ γ, (p.map fun e => (q.map fun f => if gm e.1 f.1 = γ then κ (ev e) * κ (ev f) else 0).sum).sum
      * M γ = (p.map fun e => (q.map fun f => if gm e.1 f.1 = γ then κ (ev e) * κ (ev f) * M γ else 0).sum).sum := by
    intro γ
    rw [lsum_mul_right]; refine lsum_congr _ _ _ (fun e _ => ?_)
    rw [lsum_mul_right]; refine lsum_congr _ _ _ (fun f _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun γ _ => h1 γ), ← lsum_fsum_comm]
  refine lsum_congr _ _ _ (fun e he => ?_)
  rw [← lsum_fsum_comm]
  refine lsum_congr _ _ _ (fun f hf => ?_)
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hN e he f hf))]

theorem sv_mul (p q : List Ent) (m : ℕ → ℝ) :
    sv p m * sv q m = (p.map fun e => (q.map fun f => κ (ev e) * κ (ev f) * (m e.1 * m f.1)).sum).sum := by
  rw [sv, sv, lsum_mul_right]
  refine lsum_congr _ _ _ (fun e _ => ?_)
  rw [← List.sum_map_mul_left]
  refine lsum_congr _ _ _ (fun f _ => by ring)

theorem stage_real (P : SP) (ts : List Term) (hW : 1 ≤ P.W) (hW2 : 1 ≤ P.W2)
    (hgam : ∀ i < P.n, ∀ j < P.n, gamD P i j < P.N) (hok : (stage P ts).1 = true)
    (m M : ℕ → ℝ) (hmM : ∀ i < P.n, ∀ j < P.n, m i * m j = M (gamD P i j)) :
    sv (stage P ts).2 M = (ts.map fun t => (t.2.2 : ℝ) * (sv t.1 m * sv t.2.1 m)).sum := by
  obtain ⟨hmap, hidx⟩ := stage_sound P ts hW hW2 hgam hok
  have hsv : sv (stage P ts).2 M = ∑ γ ∈ range P.N, κ (coefC (gamD P) ts γ) * M γ := by
    have : sv (stage P ts).2 M = (((stage P ts).2.map fun e => (e.1, ev e)).map fun x => κ x.2 * M x.1).sum := by
      rw [sv, List.map_map]; rfl
    rw [this, hmap, List.map_map, ← lsum_range]; rfl
  rw [hsv]
  have hκ : ∀ γ, κ (coefC (gamD P) ts γ) * M γ = (ts.map fun t => (t.2.2 : ℝ) *
      ((t.1.map fun e => (t.2.1.map fun f => if gamD P e.1 f.1 = γ then κ (ev e) * κ (ev f) else 0).sum).sum
        * M γ)).sum := by
    intro γ
    rw [coefC, map_list_sum, List.map_map, lsum_mul_right]
    refine lsum_congr _ _ _ (fun t _ => ?_)
    simp only [Function.comp, map_mul, map_natCast, κ_S]
    ring
  rw [Finset.sum_congr rfl (fun γ _ => hκ γ), ← lsum_fsum_comm]
  refine lsum_congr _ _ _ (fun t ht => ?_)
  rw [← Finset.mul_sum, inner_collapse _ _ _ _ _ (fun e he f hf => hgam _ ((hidx t ht).1 e he) _ ((hidx t ht).2 f hf)),
    sv_mul]
  congr 1
  refine lsum_congr _ _ _ (fun e he => lsum_congr _ _ _ (fun f hf => ?_))
  rw [hmM _ ((hidx t ht).1 e he) _ ((hidx t ht).2 f hf)]

end ThomsonCompact.TailC
