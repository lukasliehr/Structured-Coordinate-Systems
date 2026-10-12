import Lean_Code.PositiveTranslates.StageMachine

/-!
# Closure properties of non-negativity

`IsNonneg g` (file `StageMachine.lean`) says that the `Lᵖ` class `g` is real and
non-negative almost everywhere. It holds for interval indicators and is preserved by sums,
non-negative real multiples and translations, hence by the packet operations `packetEdit`
and `packetNoise`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞}

theorem isNonneg_zero : IsNonneg (0 : LebesgueLp p) := by
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := p) (μ := (volume : Measure ℝ))] with x hx
  rw [hx]
  exact le_rfl

theorem IsNonneg.add {f g : LebesgueLp p} (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx ha
  rw [ha]
  exact add_nonneg hfx hgx

theorem IsNonneg.smul {f : LebesgueLp p} (hf : IsNonneg f) {c : ℝ} (hc : 0 ≤ c) :
    IsNonneg (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hfx ha
  rw [ha]
  exact smul_nonneg hc hfx

theorem IsNonneg.finset_sum {ι : Type*} (s : Finset ι) (f : ι → LebesgueLp p)
    (hf : ∀ i ∈ s, IsNonneg (f i)) : IsNonneg (∑ i ∈ s, f i) := by
  have hall : ∀ᵐ x : ℝ, ∀ i ∈ s, 0 ≤ f i x := by
    simpa only [Filter.eventually_all_finset, IsNonneg] using hf
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s f] with x hx hsum
  rw [hsum]
  exact Finset.sum_nonneg hx

theorem IsNonneg.translate {f : LebesgueLp p} (hf : IsNonneg f) (a : ℝ) :
    IsNonneg (translate p a f) := by
  have hcomp := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae hf
  filter_upwards [translate_ae p a f, hcomp] with x hx hfx
  rw [hx]
  exact hfx

/-- Interval indicators are non-negative. -/
theorem isNonneg_intervalAtom (p : ℝ≥0∞) (ab : ℝ × ℝ) : IsNonneg (intervalAtom p ab) := by
  filter_upwards [intervalAtom_ae p ab] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- The edit `a ∑ⱼ T_{-Λⱼ} h` is non-negative for `a ≥ 0`, `h ≥ 0`. -/
theorem packetEdit_isNonneg {N : ℕ} (Λ : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a)
    {h : LebesgueLp p} (hh : IsNonneg h) : IsNonneg (packetEdit p Λ a h) :=
  (IsNonneg.finset_sum Finset.univ _ (fun j _ => hh.translate (-Λ j))).smul ha

/-- The remainder `T_{Λᵢ} v + a ∑_{j ≠ i} T_{Λᵢ - Λⱼ} h` is non-negative for `a ≥ 0` and
`v, h ≥ 0`. -/
theorem packetNoise_isNonneg {N : ℕ} (Λ : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a)
    {v h : LebesgueLp p} (hv : IsNonneg v) (hh : IsNonneg h) (i : Fin N) :
    IsNonneg (packetNoise p Λ a v h i) := by
  classical
  exact (hv.translate (Λ i)).add
    ((IsNonneg.finset_sum (Finset.univ.erase i) _
      (fun j _ => hh.translate (Λ i - Λ j))).smul ha)

end StructuredBases.PositiveTranslates
