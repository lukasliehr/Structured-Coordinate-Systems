import Lean_Code.SchauderTranslates.Lp.StepPartition

noncomputable section

namespace SchauderTranslates.LpConstruction

/-- Consecutive cells of any finite real breakpoint set, used to fill a
committed interval without changing its already allocated cells. -/
def breakpointCells (B : Finset ℝ) : Finset (ℝ × ℝ) :=
  (B ×ˢ B).filter (fun ab => ab.1 < ab.2 ∧ ∀ t ∈ B, t ∉ Set.Ioo ab.1 ab.2)

theorem breakpointCells_mem (B : Finset ℝ) (ab : ℝ × ℝ) :
    ab ∈ breakpointCells B ↔ (ab.1 ∈ B ∧ ab.2 ∈ B) ∧
      ab.1 < ab.2 ∧ ∀ t ∈ B, t ∉ Set.Ioo ab.1 ab.2 := by
  classical
  simp only [breakpointCells, Finset.mem_filter, Finset.mem_product]

theorem breakpointCells_disjoint (B : Finset ℝ) {ab cd : ℝ × ℝ}
    (hab : ab ∈ breakpointCells B) (hcd : cd ∈ breakpointCells B) (hne : ab ≠ cd) :
    Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2) := by
  obtain ⟨⟨ha, hb⟩, hablt, hgapab⟩ := (breakpointCells_mem B ab).mp hab
  obtain ⟨⟨hc, hd⟩, hcdlt, hgapcd⟩ := (breakpointCells_mem B cd).mp hcd
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

theorem breakpointCells_cover (B : Finset ℝ) {a b x : ℝ} (ha : a ∈ B) (hb : b ∈ B)
    (hx : x ∈ Set.Ico a b) : ∃ cd ∈ breakpointCells B, x ∈ Set.Ico cd.1 cd.2 := by
  classical
  let L := B.filter (fun t => t ≤ x)
  let R := B.filter (fun t => x < t)
  have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hx.1⟩⟩
  have hR : R.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hx.2⟩⟩
  let c := L.max' hL
  let d := R.min' hR
  have hc := Finset.mem_filter.mp (L.max'_mem hL)
  have hd := Finset.mem_filter.mp (R.min'_mem hR)
  have hgap : ∀ t ∈ B, t ∉ Set.Ioo c d := by
    intro t ht htd
    by_cases htx : t ≤ x
    · have htc : t ≤ c := L.le_max' t (Finset.mem_filter.mpr ⟨ht, htx⟩)
      exact not_lt_of_ge htc htd.1
    · have hdt : d ≤ t := R.min'_le t (Finset.mem_filter.mpr ⟨ht, lt_of_not_ge htx⟩)
      exact not_lt_of_ge hdt htd.2
  exact ⟨(c, d), (breakpointCells_mem B (c, d)).mpr
    ⟨⟨hc.1, hd.1⟩, hc.2.trans_lt hd.2, hgap⟩, ⟨hc.2, hd.2⟩⟩

/-- An interval whose endpoints are breakpoints has constant membership
on each consecutive half-open cell, including its left endpoint. -/
theorem breakpointCells_membership_constant (B : Finset ℝ) {ab : ℝ × ℝ}
    (hab : ab ∈ breakpointCells B) {l u x : ℝ} (hl : l ∈ B) (hu : u ∈ B)
    (hx : x ∈ Set.Ico ab.1 ab.2) : x ∈ Set.Ico l u ↔ ab.1 ∈ Set.Ico l u := by
  have hgap := (breakpointCells_mem B ab).mp hab |>.2.2
  constructor
  · rintro ⟨hxl, hxu⟩
    refine ⟨?_, hx.1.trans_lt hxu⟩
    by_contra! h
    exact hgap l hl ⟨h, hxl.trans_lt hx.2⟩
  · rintro ⟨hal, hau⟩
    refine ⟨hal.trans hx.1, ?_⟩
    by_contra! h
    exact hgap u hu ⟨hau, h.trans_lt hx.2⟩

end SchauderTranslates.LpConstruction
