import Lean_Code.SchauderTranslates.Lp.StepRefinement

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

structure DisjointStepData (p : ℝ≥0∞) (e : LebesgueLp p) where
  cells : Finset (ℝ × ℝ)
  value : ℝ × ℝ → ℝ
  length_pos : ∀ ab ∈ cells, ab.1 < ab.2
  value_ne_zero : ∀ ab ∈ cells, value ab ≠ 0
  disjoint : ∀ ab ∈ cells, ∀ cd ∈ cells, ab ≠ cd →
    Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2)
  representation : e = ∑ ab ∈ cells, value ab • intervalAtom p ab

theorem IsCompactStep.disjoint_data {p : ℝ≥0∞} {e : LebesgueLp p} (he : IsCompactStep p e) :
    Nonempty (DisjointStepData p e) := by
  obtain ⟨s, d, hs, hd, hrep⟩ := he.disjoint_representation
  exact ⟨⟨s, d, fun ab hab => (hs ab hab).1, fun ab hab => (hs ab hab).2, hd, hrep⟩⟩

theorem intervalAtom_supported_cell (p : ℝ≥0∞) (ab : ℝ × ℝ) :
    SupportedOn (intervalAtom p ab) (Set.Ico ab.1 ab.2) := indicatorConstLp_coeFn_notMem

theorem intervalAtom_norm_power {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (ab : ℝ × ℝ) (hab : ab.1 < ab.2) : ‖intervalAtom p ab‖ ^ p.toReal = ab.2 - ab.1 := by
  have hs : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩
  rw [norm_intervalAtom p hp0 hpfin ab, max_eq_left (sub_pos.mpr hab).le,
    one_div, Real.rpow_inv_rpow (sub_nonneg.mpr hab.le) hs]

def DisjointStepData.mass {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e)
    (ab : ℝ × ℝ) : ℝ := |D.value ab| ^ p.toReal * (ab.2 - ab.1)

theorem DisjointStepData.mass_pos {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e)
    {ab : ℝ × ℝ} (hab : ab ∈ D.cells) : 0 < D.mass ab :=
  mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (D.value_ne_zero ab hab)) _)
    (sub_pos.mpr (D.length_pos ab hab))

theorem DisjointStepData.mass_sum {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {e : LebesgueLp p} (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ∑ ab ∈ D.cells, D.mass ab = ‖e‖ ^ p.toReal := by
  conv_rhs => rw [D.representation]
  rw [norm_finset_sum_rpow D.cells _ hp0 hpfin]
  · apply Finset.sum_congr rfl
    intro ab hab
    rw [norm_real_smul_rpow, intervalAtom_norm_power hp0 hpfin ab (D.length_pos ab hab)]
    rfl
  · intro ab hab cd hcd hne
    exact ((intervalAtom_supported_cell p ab).real_smul (D.value ab)).ae_disjoint
      ((intervalAtom_supported_cell p cd).real_smul (D.value cd)) (D.disjoint ab hab cd hcd hne)

theorem DisjointStepData.mass_sum_one {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {e : LebesgueLp p} (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1) :
    ∑ ab ∈ D.cells, D.mass ab = 1 := by
  rw [D.mass_sum hp0 hpfin, he, Real.one_rpow]

theorem DisjointStepData.cells_nonempty {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {e : LebesgueLp p} (D : DisjointStepData p e) (he : ‖e‖ = 1) : D.cells.Nonempty := by
  by_contra h
  have hzero : e = 0 := by simpa [Finset.not_nonempty_iff_eq_empty.mp h] using D.representation
  simp [hzero] at he

end SchauderTranslates.LpConstruction
