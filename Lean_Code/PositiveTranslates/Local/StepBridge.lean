import Lean_Code.PositiveTranslates.Local.Defs
import Lean_Code.PositiveBiorthogonal.Statements
import Lean_Code.SchauderTranslates.Lp.IndexedIntervalStep

/-!
# From the step functions of the positive library to `IsCompactStep`

The library `Lean_Code/PositiveBiorthogonal` describes compactly supported step functions by
`PositiveBiorthogonal.CompactlySupportedStep` (almost everywhere a finite sum of indicators of
intervals `Ioc` with scalar coefficients). The translate development uses `IsCompactStep p`
(membership in the real span of the indicators of intervals `Ico`). For functions which are
real and non-negative almost everywhere the first notion implies the second; the endpoints
form a null set.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

variable {p : ℝ≥0∞}

/-- Outside a null set the intervals `Ioc a b` and `Ico a b` have the same points. -/
theorem Local.ae_mem_Ioc_iff_mem_Ico (a b : ℝ) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioc a b ↔ x ∈ Set.Ico a b := by
  have ha : ∀ᵐ x : ℝ, x ∉ ({a} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton a)
  have hb : ∀ᵐ x : ℝ, x ∉ ({b} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton b)
  filter_upwards [ha, hb] with x hxa hxb
  have hxa' : x ≠ a := hxa
  have hxb' : x ≠ b := hxb
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.le, lt_of_le_of_ne h2 hxb'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hxa'), h2.le⟩

/-- The root vector of the positive library is the interval atom of `[0, 1)`. -/
theorem gridUnit_indicator_eq_intervalAtom (p : ℝ≥0∞) :
    ((PositiveBiorthogonal.gridUnit 0).indicator : LebesgueLp p) = intervalAtom p (0, 1) := by
  apply Lp.ext
  have hc : (PositiveBiorthogonal.gridUnit 0).carrier = Set.Ioc (0 : ℝ) 1 := by
    simp [PositiveBiorthogonal.gridUnit, PositiveBiorthogonal.IntervalCell.carrier]
  filter_upwards [(PositiveBiorthogonal.gridUnit 0).coe_indicator (𝕜 := ℂ) (p := p),
    intervalAtom_ae p (0, 1), ae_mem_Ioc_iff_mem_Ico 0 1] with x h1 h2 h3
  rw [h1, h2, hc]
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h3.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt h3.mp hx)]

/-- Non-negativity in the sense of the positive library is `IsNonneg`. -/
theorem Local.isNonneg_of_nonnegative {f : LebesgueLp p}
    (hf : PositiveBiorthogonal.Nonnegative f) : IsNonneg f := hf

/-- A compactly supported step function in the sense of the positive library which is
non-negative almost everywhere is a compact step function in the sense of the translate
development: it is a finite real combination of interval atoms. -/
theorem isCompactStep_of_step_of_nonneg {f : LebesgueLp p}
    (hstep : PositiveBiorthogonal.CompactlySupportedStep f)
    (hpos : PositiveBiorthogonal.Nonnegative f) : IsCompactStep p f := by
  obtain ⟨m, a, b, c, hc⟩ := hstep
  have hrep : f = indexedIntervalStep p (fun j => (a j, b j)) (fun j => (c j).re) := by
    apply Lp.ext
    have hend : ∀ᵐ x : ℝ, ∀ j : Fin m, (x ∈ Set.Ioc (a j) (b j) ↔ x ∈ Set.Ico (a j) (b j)) :=
      ae_all_iff.mpr (fun j => ae_mem_Ioc_iff_mem_Ico (a j) (b j))
    filter_upwards [hc, hpos, hend,
      indexedIntervalStep_ae p (fun j => (a j, b j)) (fun j => (c j).re)] with x hx hx0 hxe hxs
    rw [hxs]
    have hre : f x = ((f x).re : ℂ) := by
      have h := Complex.nonneg_iff.mp hx0
      apply Complex.ext
      · simp
      · simp [← h.2]
    rw [hre, hx, Complex.re_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : x ∈ Set.Ico (a j) (b j)
    · simp [Set.indicator_of_mem hj, Set.indicator_of_mem ((hxe j).mpr hj)]
    · simp [Set.indicator_of_notMem hj, Set.indicator_of_notMem (mt (hxe j).mp hj)]
  rw [hrep]
  exact indexedIntervalStep_isCompactStep _ _ _

end StructuredBases.PositiveTranslates
