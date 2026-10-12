import Lean_Code.SchauderTranslates.Lp.StepPartition

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def intervalSumValue (s : Finset (ℝ × ℝ)) (d : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ ab ∈ s, d ab * (Set.Ico ab.1 ab.2).indicator (fun _ => (1 : ℝ)) x

theorem intervalSumValue_ae (p : ℝ≥0∞) (s : Finset (ℝ × ℝ)) (d : ℝ × ℝ → ℝ) :
    ((∑ ab ∈ s, d ab • intervalAtom p ab : LebesgueLp p) : ℝ → ℂ) =ᵐ[volume]
      fun x => (intervalSumValue s d x : ℂ) := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ ab ∈ s,
      (d ab • intervalAtom p ab) x =
        ((d ab * (Set.Ico ab.1 ab.2).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
    simp only [Filter.eventually_all_finset]
    intro ab _
    filter_upwards [intervalAtom_ae p ab, Lp.coeFn_smul (d ab) (intervalAtom p ab)] with x hi hs
    rw [hs, Pi.smul_apply, hi, Complex.real_smul]
    by_cases hx : x ∈ Set.Ico ab.1 ab.2 <;> simp [hx]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s (fun ab => d ab • intervalAtom p ab)] with x hall hx
  rw [hx, intervalSumValue, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun ab hab => hall ab hab)

theorem compactStepValue_refinement (c : (ℝ × ℝ) →₀ ℝ) (x : ℝ) :
    compactStepValue c x = intervalSumValue (compactStepCells c)
      (fun ab => compactStepValue c ab.1) x := by
  classical
  by_cases hcell : ∃ ab ∈ compactStepCells c, x ∈ Set.Ico ab.1 ab.2
  · obtain ⟨ab, hab, hx⟩ := hcell
    rw [intervalSumValue, Finset.sum_eq_single ab]
    · rw [compactStepCells_constant c hab hx]
      simp [hx]
    · intro cd hcd hne
      have hxc : x ∉ Set.Ico cd.1 cd.2 := fun hc =>
        Set.disjoint_left.mp (compactStepCells_disjoint c hcd hab hne) hc hx
      simp [hxc]
    · exact fun h => False.elim (h hab)
  · have hout (ab : ℝ × ℝ) (hab : ab ∈ c.support) : x ∉ Set.Ico ab.1 ab.2 :=
      fun hx => hcell (compactStepCells_cover_original c hab hx)
    have hzero : compactStepValue c x = 0 := by
      apply Finset.sum_eq_zero
      intro ab hab
      simp [hout ab hab]
    rw [hzero, intervalSumValue]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    have hx : x ∉ Set.Ico ab.1 ab.2 := fun hx => hcell ⟨ab, hab, hx⟩
    simp [hx]

theorem compactStepLp_refinement (p : ℝ≥0∞) (c : (ℝ × ℝ) →₀ ℝ) :
    (∑ ab ∈ c.support, c ab • intervalAtom p ab : LebesgueLp p) =
      ∑ ab ∈ compactStepCells c, compactStepValue c ab.1 • intervalAtom p ab := by
  apply Lp.ext
  filter_upwards [compactStepValue_ae p c,
    intervalSumValue_ae p (compactStepCells c) (fun ab => compactStepValue c ab.1)] with x hl hr
  rw [hl, hr, compactStepValue_refinement]

def compactStepNonzeroCells (c : (ℝ × ℝ) →₀ ℝ) : Finset (ℝ × ℝ) :=
  (compactStepCells c).filter (fun ab => compactStepValue c ab.1 ≠ 0)

theorem compactStepLp_nonzero_refinement (p : ℝ≥0∞) (c : (ℝ × ℝ) →₀ ℝ) :
    (∑ ab ∈ c.support, c ab • intervalAtom p ab : LebesgueLp p) =
      ∑ ab ∈ compactStepNonzeroCells c, compactStepValue c ab.1 • intervalAtom p ab := by
  classical
  rw [compactStepLp_refinement, compactStepNonzeroCells]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ab _
  by_cases h : compactStepValue c ab.1 = 0 <;> simp [h]

/-- Every compact real step function has a finite disjoint representation
on positive-length intervals with nonzero real values. This is obtained
from the existing algebraic step predicate, not assumed as a new input. -/
theorem IsCompactStep.disjoint_representation {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) :
    ∃ (s : Finset (ℝ × ℝ)) (d : ℝ × ℝ → ℝ),
      (∀ ab ∈ s, ab.1 < ab.2 ∧ d ab ≠ 0) ∧
      (∀ ab ∈ s, ∀ cd ∈ s, ab ≠ cd → Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2)) ∧
      f = ∑ ab ∈ s, d ab • intervalAtom p ab := by
  classical
  obtain ⟨c, hc⟩ := hf.finite_representation
  refine ⟨compactStepNonzeroCells c, fun ab => compactStepValue c ab.1, ?_, ?_, ?_⟩
  · intro ab hab
    obtain ⟨hab, hn⟩ := Finset.mem_filter.mp hab
    exact ⟨((compactStepCells_mem c ab).mp hab).2.1, hn⟩
  · intro ab hab cd hcd hne
    exact compactStepCells_disjoint c (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hcd).1 hne
  · rw [hc, compactStepLp_nonzero_refinement]

end SchauderTranslates.LpConstruction
