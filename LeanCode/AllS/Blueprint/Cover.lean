import Blueprint.Target

noncomputable section
namespace Blueprint

/-- Closed endpoints in increasing left-endpoint order; exact rational literals. -/
def lower : Fin 30 → ℝ := ![0, (2 / 5), (13 / 10), (19 / 10), (12 / 5), (14 / 5), (19 / 5), (39 / 10), (49 / 10), (11 / 2), (61 / 10), (67 / 10), (36 / 5), 8, (177 / 20), (19 / 2), (101 / 10), (87 / 8), 15, 16, (43 / 2), (55 / 2), (67 / 2), (79 / 2), (167 / 4), (97 / 2), 50, 62, 81, 87]
def upper : Fin 30 → ℝ := ![(2 / 5), (8 / 5), (19 / 10), (5 / 2), (14 / 5), (19 / 5), (21 / 5), (49 / 10), (11 / 2), (61 / 10), (67 / 10), (73 / 10), 8, (89 / 10), (191 / 20), (101 / 10), 11, 15, 16, (43 / 2), (55 / 2), (67 / 2), (79 / 2), (85 / 2), (197 / 4), (103 / 2), 62, 82, 87, 97]

def CellSpec (i : Fin 30) : Prop :=
  ∀ s : ℝ, 0 ≤ s → lower i ≤ s → s ≤ upper i → ∀ a : ℝ,
    a ∈ Set.Ioo (0 : ℝ) 1 → Thomson.F s a = 0 →
      Thomson.IsUniqueMinimizer s (Thomson.X a)

theorem cover (s : ℝ) (hs0 : 0 ≤ s) (hs97 : s ≤ 97) :
    ∃ i : Fin 30, lower i ≤ s ∧ s ≤ upper i := by
  by_contra h
  push Not at h
  have h0 : (2 / 5) < s := by
    have hx := h (0 : Fin 30)
    change (0 : ℝ) ≤ s → (2 / 5 : ℝ) < s at hx
    exact hx (by linarith [hs0])
  have h1 : (8 / 5) < s := by
    have hx := h (1 : Fin 30)
    change (2 / 5 : ℝ) ≤ s → (8 / 5 : ℝ) < s at hx
    exact hx (by linarith [h0])
  have h2 : (19 / 10) < s := by
    have hx := h (2 : Fin 30)
    change (13 / 10 : ℝ) ≤ s → (19 / 10 : ℝ) < s at hx
    exact hx (by linarith [h1])
  have h3 : (5 / 2) < s := by
    have hx := h (3 : Fin 30)
    change (19 / 10 : ℝ) ≤ s → (5 / 2 : ℝ) < s at hx
    exact hx (by linarith [h2])
  have h4 : (14 / 5) < s := by
    have hx := h (4 : Fin 30)
    change (12 / 5 : ℝ) ≤ s → (14 / 5 : ℝ) < s at hx
    exact hx (by linarith [h3])
  have h5 : (19 / 5) < s := by
    have hx := h (5 : Fin 30)
    change (14 / 5 : ℝ) ≤ s → (19 / 5 : ℝ) < s at hx
    exact hx (by linarith [h4])
  have h6 : (21 / 5) < s := by
    have hx := h (6 : Fin 30)
    change (19 / 5 : ℝ) ≤ s → (21 / 5 : ℝ) < s at hx
    exact hx (by linarith [h5])
  have h7 : (49 / 10) < s := by
    have hx := h (7 : Fin 30)
    change (39 / 10 : ℝ) ≤ s → (49 / 10 : ℝ) < s at hx
    exact hx (by linarith [h6])
  have h8 : (11 / 2) < s := by
    have hx := h (8 : Fin 30)
    change (49 / 10 : ℝ) ≤ s → (11 / 2 : ℝ) < s at hx
    exact hx (by linarith [h7])
  have h9 : (61 / 10) < s := by
    have hx := h (9 : Fin 30)
    change (11 / 2 : ℝ) ≤ s → (61 / 10 : ℝ) < s at hx
    exact hx (by linarith [h8])
  have h10 : (67 / 10) < s := by
    have hx := h (10 : Fin 30)
    change (61 / 10 : ℝ) ≤ s → (67 / 10 : ℝ) < s at hx
    exact hx (by linarith [h9])
  have h11 : (73 / 10) < s := by
    have hx := h (11 : Fin 30)
    change (67 / 10 : ℝ) ≤ s → (73 / 10 : ℝ) < s at hx
    exact hx (by linarith [h10])
  have h12 : 8 < s := by
    have hx := h (12 : Fin 30)
    change (36 / 5 : ℝ) ≤ s → (8 : ℝ) < s at hx
    exact hx (by linarith [h11])
  have h13 : (89 / 10) < s := by
    have hx := h (13 : Fin 30)
    change (8 : ℝ) ≤ s → (89 / 10 : ℝ) < s at hx
    exact hx (by linarith [h12])
  have h14 : (191 / 20) < s := by
    have hx := h (14 : Fin 30)
    change (177 / 20 : ℝ) ≤ s → (191 / 20 : ℝ) < s at hx
    exact hx (by linarith [h13])
  have h15 : (101 / 10) < s := by
    have hx := h (15 : Fin 30)
    change (19 / 2 : ℝ) ≤ s → (101 / 10 : ℝ) < s at hx
    exact hx (by linarith [h14])
  have h16 : 11 < s := by
    have hx := h (16 : Fin 30)
    change (101 / 10 : ℝ) ≤ s → (11 : ℝ) < s at hx
    exact hx (by linarith [h15])
  have h17 : 15 < s := by
    have hx := h (17 : Fin 30)
    change (87 / 8 : ℝ) ≤ s → (15 : ℝ) < s at hx
    exact hx (by linarith [h16])
  have h18 : 16 < s := by
    have hx := h (18 : Fin 30)
    change (15 : ℝ) ≤ s → (16 : ℝ) < s at hx
    exact hx (by linarith [h17])
  have h19 : (43 / 2) < s := by
    have hx := h (19 : Fin 30)
    change (16 : ℝ) ≤ s → (43 / 2 : ℝ) < s at hx
    exact hx (by linarith [h18])
  have h20 : (55 / 2) < s := by
    have hx := h (20 : Fin 30)
    change (43 / 2 : ℝ) ≤ s → (55 / 2 : ℝ) < s at hx
    exact hx (by linarith [h19])
  have h21 : (67 / 2) < s := by
    have hx := h (21 : Fin 30)
    change (55 / 2 : ℝ) ≤ s → (67 / 2 : ℝ) < s at hx
    exact hx (by linarith [h20])
  have h22 : (79 / 2) < s := by
    have hx := h (22 : Fin 30)
    change (67 / 2 : ℝ) ≤ s → (79 / 2 : ℝ) < s at hx
    exact hx (by linarith [h21])
  have h23 : (85 / 2) < s := by
    have hx := h (23 : Fin 30)
    change (79 / 2 : ℝ) ≤ s → (85 / 2 : ℝ) < s at hx
    exact hx (by linarith [h22])
  have h24 : (197 / 4) < s := by
    have hx := h (24 : Fin 30)
    change (167 / 4 : ℝ) ≤ s → (197 / 4 : ℝ) < s at hx
    exact hx (by linarith [h23])
  have h25 : (103 / 2) < s := by
    have hx := h (25 : Fin 30)
    change (97 / 2 : ℝ) ≤ s → (103 / 2 : ℝ) < s at hx
    exact hx (by linarith [h24])
  have h26 : 62 < s := by
    have hx := h (26 : Fin 30)
    change (50 : ℝ) ≤ s → (62 : ℝ) < s at hx
    exact hx (by linarith [h25])
  have h27 : 82 < s := by
    have hx := h (27 : Fin 30)
    change (62 : ℝ) ≤ s → (82 : ℝ) < s at hx
    exact hx (by linarith [h26])
  have h28 : 87 < s := by
    have hx := h (28 : Fin 30)
    change (81 : ℝ) ≤ s → (87 : ℝ) < s at hx
    exact hx (by linarith [h27])
  have h29 : 97 < s := by
    have hx := h (29 : Fin 30)
    change (87 : ℝ) ≤ s → (97 : ℝ) < s at hx
    exact hx (by linarith [h28])
  linarith [h29]

theorem finite_of_cells (hc : ∀ i : Fin 30, CellSpec i) : FiniteSpec := by
  intro s hs0 hs97 a ha hF
  obtain ⟨i, hlo, hhi⟩ := cover s hs0 hs97
  exact hc i s hs0 hlo hhi a ha hF

#print axioms cover
#print axioms finite_of_cells
end Blueprint
