import Lean_Code.SchauderTranslates.Lp.StepFunctions

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- A finite interval formula provides a real representative of every
element of the algebraic real compact-step space. -/
def compactStepValue (c : (ℝ × ℝ) →₀ ℝ) (x : ℝ) : ℝ :=
  ∑ ab ∈ c.support, c ab * (Set.Ico ab.1 ab.2).indicator (fun _ => (1 : ℝ)) x

theorem compactStepValue_measurable (c : (ℝ × ℝ) →₀ ℝ) : Measurable (compactStepValue c) := by
  classical
  exact Finset.measurable_sum _ (fun ab _ =>
    measurable_const.mul (measurable_const.indicator measurableSet_Ico))

theorem compactStepValue_ae (p : ℝ≥0∞) (c : (ℝ × ℝ) →₀ ℝ) :
    ((∑ ab ∈ c.support, c ab • intervalAtom p ab : LebesgueLp p) : ℝ → ℂ) =ᵐ[volume]
      fun x => (compactStepValue c x : ℂ) := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ ab ∈ c.support,
      (c ab • intervalAtom p ab) x =
        ((c ab * (Set.Ico ab.1 ab.2).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
    simp only [Filter.eventually_all_finset]
    intro ab _
    filter_upwards [intervalAtom_ae p ab, Lp.coeFn_smul (c ab) (intervalAtom p ab)] with x hi hs
    rw [hs, Pi.smul_apply, hi, Complex.real_smul]
    by_cases hx : x ∈ Set.Ico ab.1 ab.2 <;> simp [hx]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum c.support (fun ab => c ab • intervalAtom p ab)]
    with x hall hx
  rw [hx, compactStepValue, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun ab hab => hall ab hab)

theorem IsCompactStep.finite_representation {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) :
    ∃ c : (ℝ × ℝ) →₀ ℝ, f = ∑ ab ∈ c.support, c ab • intervalAtom p ab := by
  change f ∈ Submodule.span ℝ (Set.range (intervalAtom p)) at hf
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  exact ⟨c, hc.symm⟩

theorem IsCompactStep.real_representative {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) :
    ∃ c : (ℝ × ℝ) →₀ ℝ, (f : ℝ → ℂ) =ᵐ[volume] fun x => (compactStepValue c x : ℂ) := by
  obtain ⟨c, rfl⟩ := hf.finite_representation
  exact ⟨c, compactStepValue_ae p c⟩

def compactStepBreakpoints (c : (ℝ × ℝ) →₀ ℝ) : Finset ℝ :=
  c.support.biUnion (fun ab => {ab.1, ab.2})

theorem compactStepBreakpoints_left (c : (ℝ × ℝ) →₀ ℝ) {ab : ℝ × ℝ} (hab : ab ∈ c.support) :
    ab.1 ∈ compactStepBreakpoints c := by
  classical
  exact Finset.mem_biUnion.mpr ⟨ab, hab, by simp⟩

theorem compactStepBreakpoints_right (c : (ℝ × ℝ) →₀ ℝ) {ab : ℝ × ℝ} (hab : ab ∈ c.support) :
    ab.2 ∈ compactStepBreakpoints c := by
  classical
  exact Finset.mem_biUnion.mpr ⟨ab, hab, by simp⟩

/-- Between consecutive breakpoints every original interval indicator,
and hence the whole representative, is constant. -/
theorem compactStepValue_constant_between_breakpoints (c : (ℝ × ℝ) →₀ ℝ)
    {a b x : ℝ} (hx : x ∈ Set.Ico a b)
    (hgap : ∀ t ∈ compactStepBreakpoints c, t ∉ Set.Ioo a b) :
    compactStepValue c x = compactStepValue c a := by
  classical
  apply Finset.sum_congr rfl
  intro ab hab
  have hl := hgap ab.1 (compactStepBreakpoints_left c hab)
  have hr := hgap ab.2 (compactStepBreakpoints_right c hab)
  have hi : x ∈ Set.Ico ab.1 ab.2 ↔ a ∈ Set.Ico ab.1 ab.2 := by
    constructor
    · rintro ⟨hxl, hxr⟩
      refine ⟨?_, hx.1.trans_lt hxr⟩
      by_contra! h
      exact hl ⟨h, hxl.trans_lt hx.2⟩
    · rintro ⟨hal, har⟩
      refine ⟨hal.trans hx.1, ?_⟩
      by_contra! h
      exact hr ⟨har, h.trans_lt hx.2⟩
  by_cases ha : a ∈ Set.Ico ab.1 ab.2
  · simp [ha, hi.mpr ha]
  · simp [ha, mt hi.mp ha]

end SchauderTranslates.LpConstruction
