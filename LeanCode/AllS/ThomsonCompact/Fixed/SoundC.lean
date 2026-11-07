import ThomsonCompact.Fixed.SoundSem
import Mathlib.Tactic.FieldSimp

/-!
# Canonical columns: the coefficient formula (workstream F4)

Pure algebra, degree-generic. If the raw column matrix of a block satisfies `K u r = κ_{r,u}(a) / (S_r δ(a))`
(`κ_{r,u} = kapE L b r u`, zero for absent raw rows) and the raw tensor coefficients are
`Z u v = zsum L b u v code / rden`, then

  `mult · Σ_{u,v < m} K u r · K v c · Z u v = ncomp L b r c mult code (a) / (S_r S_c rden δ(a)²)`,

i.e. the canonical column coefficient is the stored `N` polynomial divided by `Δ_k`.
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-- Strictly increasing indices `≥ lo`. -/
def IncI : Nat → List Nat → Prop
  | _, [] => True
  | lo, x :: xs => lo ≤ x ∧ IncI (x + 1) xs

theorem incI_of_inc : ∀ {lo : Nat} (l : List (Nat × Bool × Nat)) (lc : List (Nat × List ℤ)),
    Inc lo l → l.map Prod.fst = lc.map Prod.fst → IncI lo (lc.map Prod.fst)
  | _, [], [], _, _ => trivial
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h
  | lo, e :: es, f :: fs, hi, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    refine ⟨h.1 ▸ hi.head, ?_⟩
    rw [← h.1]
    exact incI_of_inc es fs hi.tail h.2

theorem lookC_cons (e : Nat × List ℤ) (es : List (Nat × List ℤ)) (u : Nat) :
    lookC (e :: es) u = if e.1 = u then e.2 else lookC es u := by
  unfold lookC
  by_cases h : e.1 = u <;> simp [List.find?_cons, h]

theorem lookC_lt : ∀ {lo : Nat} (lc : List (Nat × List ℤ)), IncI lo (lc.map Prod.fst) → ∀ u, u < lo → lookC lc u = []
  | _, [], _, u, _ => by simp [lookC]
  | lo, e :: es, h, u, hu => by
    rw [lookC_cons, if_neg (by have := h.1; omega)]
    exact lookC_lt es h.2 u (by have := h.1; omega)

/-- A `range` sum over a sparse coefficient list. -/
theorem sum_lookC (m : ℕ) (a : ℝ) (F : ℕ → ℝ → ℝ) (hF : ∀ u, F u 0 = 0) :
    ∀ {lo : Nat} (lc : List (Nat × List ℤ)), IncI lo (lc.map Prod.fst) → (∀ e ∈ lc, e.1 < m) →
      ∑ u ∈ Finset.range m, F u (evalZ (lookC lc u) a) = (lc.map fun e => F e.1 (evalZ e.2 a)).sum
  | _, [], _, _ => by simp [lookC, evalZ, hF]
  | lo, e :: es, h, hb => by
    have ih := sum_lookC m a F hF es h.2 (fun x hx => hb x (by simp [hx]))
    have he : e.1 < m := hb e (by simp)
    have h0 : lookC es e.1 = [] := lookC_lt es h.2 e.1 (by omega)
    have split : ∀ u, F u (evalZ (lookC (e :: es) u) a) =
        (if u = e.1 then F e.1 (evalZ e.2 a) else 0) + F u (evalZ (lookC es u) a) := by
      intro u
      rw [lookC_cons]
      by_cases hu : u = e.1
      · subst hu; rw [if_pos rfl, if_pos rfl, h0]; simp [evalZ, hF]
      · rw [if_neg (Ne.symm hu), if_neg hu, zero_add]
    rw [Finset.sum_congr rfl (fun u _ => split u), Finset.sum_add_distrib, ih]
    simp only [Finset.sum_ite_eq', Finset.mem_range, he, if_true, List.map_cons, List.sum_cons]

theorem sum_mul_list {α : Type*} (l : List α) (g : α → ℝ) (c : ℝ) :
    c * (l.map g).sum = (l.map fun x => c * g x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

theorem sum_mul_list' {α : Type*} (l : List α) (g : α → ℝ) (c : ℝ) :
    (l.map g).sum * c = (l.map fun x => g x * c).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_mul]

theorem evalZ_ncomp (L : LTab) (b r c mult code : Nat) (a : ℝ) :
    evalZ (ncomp L b r c mult code) a = ((kapC L b r).map fun u => ((kapC L b c).map fun v =>
      ((mult : ℤ) * zsum L b u.1 v.1 code : ℝ) * (evalZ u.2 a * evalZ v.2 a)).sum).sum := by
  unfold ncomp
  rw [evalZ_sumL, List.map_map]
  congr 1; apply List.map_congr_left; intro u _
  simp only [Function.comp, evalZ_sumL, List.map_map]
  congr 1; apply List.map_congr_left; intro v _
  simp only [Function.comp, evalZ_scaleL, evalZ_convL]
  push_cast; ring

/-- **The coefficient formula** of a canonical column. -/
theorem coef_formula (L : LTab) (b r c mult code m : Nat) (a δ Sr Sc rden : ℝ) (hδ : δ ≠ 0) (hr : Sr ≠ 0) (hc : Sc ≠ 0)
    (hd : rden ≠ 0) (Kr Kc : ℕ → ℝ) (Z : ℕ → ℕ → ℝ)
    (hKr : ∀ u, u < m → Kr u = evalZ (kapE L b r u) a / (Sr * δ))
    (hKc : ∀ v, v < m → Kc v = evalZ (kapE L b c v) a / (Sc * δ))
    (hZ : ∀ u v, Z u v = (zsum L b u v code : ℝ) / rden)
    (ir : IncI 0 ((kapC L b r).map Prod.fst)) (ic : IncI 0 ((kapC L b c).map Prod.fst))
    (br : ∀ e ∈ kapC L b r, e.1 < m) (bc : ∀ e ∈ kapC L b c, e.1 < m) :
    (mult : ℝ) * ∑ u ∈ Finset.range m, ∑ v ∈ Finset.range m, Kr u * Kc v * Z u v =
      evalZ (ncomp L b r c mult code) a / (Sr * Sc * rden * δ ^ 2) := by
  have e1 : ∀ u ∈ Finset.range m, ∑ v ∈ Finset.range m, Kr u * Kc v * Z u v =
      ∑ v ∈ Finset.range m, (fun v x => evalZ (kapE L b r u) a / (Sr * δ) * (x / (Sc * δ)) *
        ((zsum L b u v code : ℝ) / rden)) v (evalZ (lookC (kapC L b c) v) a) := by
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [hKr u (Finset.mem_range.mp hu), hKc v (Finset.mem_range.mp hv), hZ]
    rfl
  rw [Finset.sum_congr rfl e1]
  have e2 : ∀ u ∈ Finset.range m, ∑ v ∈ Finset.range m, (fun v x => evalZ (kapE L b r u) a / (Sr * δ) *
        (x / (Sc * δ)) * ((zsum L b u v code : ℝ) / rden)) v (evalZ (lookC (kapC L b c) v) a) =
      ((kapC L b c).map fun f => evalZ (kapE L b r u) a / (Sr * δ) * (evalZ f.2 a / (Sc * δ)) *
        ((zsum L b u f.1 code : ℝ) / rden)).sum := by
    intro u _
    exact sum_lookC m a (fun v x => evalZ (kapE L b r u) a / (Sr * δ) * (x / (Sc * δ)) *
      ((zsum L b u v code : ℝ) / rden)) (fun v => by simp) (kapC L b c) ic bc
  rw [Finset.sum_congr rfl e2]
  have e3 := sum_lookC m a (fun u x => ((kapC L b c).map fun f => x / (Sr * δ) * (evalZ f.2 a / (Sc * δ)) *
      ((zsum L b u f.1 code : ℝ) / rden)).sum) (fun u => by simp) (kapC L b r) ir br
  simp only [kapE] at e3 ⊢
  rw [e3, evalZ_ncomp, div_eq_mul_inv, sum_mul_list, sum_mul_list']
  congr 1; apply List.map_congr_left; intro e _
  rw [sum_mul_list, sum_mul_list']
  congr 1; apply List.map_congr_left; intro f _
  field_simp
  push_cast
  ring

#print axioms coef_formula

end ThomsonCompact.Fixed
