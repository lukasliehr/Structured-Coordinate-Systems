import Lean_Code.SchauderTranslates.Lp.StepRepresentation

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Consecutive pairs of the finite breakpoint set give bounded,
positive-length cells, including possible cells on which the value is zero. -/
def compactStepCells (c : (ℝ × ℝ) →₀ ℝ) : Finset (ℝ × ℝ) :=
  ((compactStepBreakpoints c) ×ˢ (compactStepBreakpoints c)).filter
    (fun ab => ab.1 < ab.2 ∧ ∀ t ∈ compactStepBreakpoints c, t ∉ Set.Ioo ab.1 ab.2)

theorem compactStepCells_mem (c : (ℝ × ℝ) →₀ ℝ) (ab : ℝ × ℝ) :
    ab ∈ compactStepCells c ↔
    (ab.1 ∈ compactStepBreakpoints c ∧ ab.2 ∈ compactStepBreakpoints c) ∧
      ab.1 < ab.2 ∧ ∀ t ∈ compactStepBreakpoints c, t ∉ Set.Ioo ab.1 ab.2 := by
  classical
  rcases ab with ⟨a, b⟩
  simp only [compactStepCells, Finset.mem_filter, Finset.mem_product]

theorem compactStepCells_constant (c : (ℝ × ℝ) →₀ ℝ) {ab : ℝ × ℝ}
    (hab : ab ∈ compactStepCells c) {x : ℝ} (hx : x ∈ Set.Ico ab.1 ab.2) :
    compactStepValue c x = compactStepValue c ab.1 :=
  compactStepValue_constant_between_breakpoints c hx ((compactStepCells_mem c ab).mp hab).2.2

theorem compactStepCells_disjoint (c : (ℝ × ℝ) →₀ ℝ) {ab cd : ℝ × ℝ}
    (hab : ab ∈ compactStepCells c) (hcd : cd ∈ compactStepCells c) (hne : ab ≠ cd) :
    Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2) := by
  obtain ⟨⟨ha, hb⟩, hablt, hgapab⟩ := (compactStepCells_mem c ab).mp hab
  obtain ⟨⟨hc, hd⟩, hcdlt, hgapcd⟩ := (compactStepCells_mem c cd).mp hcd
  rcases lt_trichotomy ab.1 cd.1 with hac | hac | hca
  · have hbc : ab.2 ≤ cd.1 := by
      by_contra! h
      exact hgapab cd.1 hc ⟨hac, h⟩
    exact Set.disjoint_left.mpr (fun _ hx hy => not_lt_of_ge (hbc.trans hy.1) hx.2)
  · have hbd : ab.2 = cd.2 := by
      rcases lt_trichotomy ab.2 cd.2 with hbd | hbd | hdb
      · exact False.elim (hgapcd ab.2 hb ⟨hac ▸ hablt, hbd⟩)
      · exact hbd
      · exact False.elim (hgapab cd.2 hd ⟨hac.symm ▸ hcdlt, hdb⟩)
    exact False.elim (hne (Prod.ext hac hbd))
  · have hda : cd.2 ≤ ab.1 := by
      by_contra! h
      exact hgapcd ab.1 ha ⟨hca, h⟩
    exact Set.disjoint_left.mpr (fun _ hx hy => not_lt_of_ge (hda.trans hx.1) hy.2)

/-- Every point of an original interval lies in a consecutive breakpoint
cell. The largest breakpoint at most x and the smallest one above x give
the half-open cell, so no endpoint exception is needed. -/
theorem compactStepCells_cover_original (c : (ℝ × ℝ) →₀ ℝ) {ab : ℝ × ℝ}
    (hab : ab ∈ c.support) {x : ℝ} (hx : x ∈ Set.Ico ab.1 ab.2) :
    ∃ cd ∈ compactStepCells c, x ∈ Set.Ico cd.1 cd.2 := by
  classical
  let B := compactStepBreakpoints c
  let L := B.filter (fun t => t ≤ x)
  let R := B.filter (fun t => x < t)
  have hL : L.Nonempty := ⟨ab.1, Finset.mem_filter.mpr ⟨compactStepBreakpoints_left c hab, hx.1⟩⟩
  have hR : R.Nonempty := ⟨ab.2, Finset.mem_filter.mpr ⟨compactStepBreakpoints_right c hab, hx.2⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha := Finset.mem_filter.mp (L.max'_mem hL)
  have hb := Finset.mem_filter.mp (R.min'_mem hR)
  have hgap : ∀ t ∈ B, t ∉ Set.Ioo a b := by
    intro t ht htab
    by_cases htx : t ≤ x
    · have hta : t ≤ a := L.le_max' t (Finset.mem_filter.mpr ⟨ht, htx⟩)
      exact not_lt_of_ge hta htab.1
    · have hbt : b ≤ t := R.min'_le t (Finset.mem_filter.mpr ⟨ht, lt_of_not_ge htx⟩)
      exact not_lt_of_ge hbt htab.2
  exact ⟨(a, b), (compactStepCells_mem c (a, b)).mpr
    ⟨⟨ha.1, hb.1⟩, ha.2.trans_lt hb.2, hgap⟩, ⟨ha.2, hb.2⟩⟩

end SchauderTranslates.LpConstruction
