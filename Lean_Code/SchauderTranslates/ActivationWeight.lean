import Lean_Code.SchauderTranslates.InitialScalar
import Lean_Code.SchauderTranslates.ActivationSet

noncomputable section
open MeasureTheory
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- An inversion-compatible complex integrand has a real integral. -/
theorem integral_real_of_neg_conj {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsNegInvariant] (f : G → ℂ)
    (h : ∀ x, f (-x) = star (f x)) : (∫ x, f x ∂μ).im = 0 := by
  have he : star (∫ x, f x ∂μ) = ∫ x, f x ∂μ := by
    change (starRingEnd ℂ) (∫ x, f x ∂μ) = _
    rw [← integral_conj]
    have he := integral_neg_eq_self f μ
    simp_rw [h, Complex.star_def] at he
    exact he
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

instance torusMeasure_negInvariant (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  exact Measure.pi.isNegInvariant (fun _ : Fin d => AddCircle.haarAddCircle)

/-- Product-space density activating the old block on a centered circle interval. -/
def activatedDensity {d : ℕ} (w : TorusWeight d) (p : ℝ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) : ℝ :=
  if z.2 ∈ activationSet p then w.density z.1 else 1

theorem activatedDensity_formula {d : ℕ} (w : TorusWeight d) (p : ℝ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) :
    activatedDensity w p z =
      1 - (activationSet p).indicator (fun _ => (1 : ℝ)) z.2 * (1 - w.density z.1) := by
  by_cases hz : z.2 ∈ activationSet p <;> simp [activatedDensity, hz]

theorem activatedDensity_measurable {d : ℕ} (w : TorusWeight d) (p : ℝ) :
    Measurable (activatedDensity w p) :=
  (w.measurable.comp measurable_fst).ite
    ((activationSet_measurable p).preimage measurable_snd) measurable_const

theorem activatedDensity_bounds {d : ℕ} (w : TorusWeight d) (p : ℝ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) :
    0 < activatedDensity w p z ∧ activatedDensity w p z ≤ 1 := by
  unfold activatedDensity
  split_ifs
  · exact ⟨w.positive _, w.le_one _⟩
  · exact ⟨zero_lt_one, le_rfl⟩

theorem activatedDensity_floor {d : ℕ} (w : TorusWeight d) {b : ℝ}
    (hb : b ≤ 1) (hw : ∀ x, b ≤ w.density x) (p : ℝ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) : b ≤ activatedDensity w p z := by
  unfold activatedDensity
  split_ifs
  · exact hw _
  · exact hb

theorem activatedDensity_even {d n : ℕ} (s : ScalarData d n) (hs : s.IsEven)
    (p : ℝ) (z : UnitAddTorus (Fin d) × UnitAddCircle) :
    activatedDensity s.toTorusWeight p (-z) = activatedDensity s.toTorusWeight p z := by
  simp only [activatedDensity, Prod.fst_neg, Prod.snd_neg, activationSet_neg_mem]
  rw [hs z.1]

theorem activatedDensity_integrable {d : ℕ} (w : TorusWeight d) (p : ℝ) :
    Integrable (activatedDensity w p) ((torusMeasure d).prod AddCircle.haarAddCircle) :=
  Integrable.of_bound (activatedDensity_measurable w p).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (activatedDensity_bounds w p z).1]
      exact (activatedDensity_bounds w p z).2))

/-- The mass is `1 - p (1-m)`, without normalizing the old density. -/
theorem activatedDensity_mass {d : ℕ} (w : TorusWeight d) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ z, activatedDensity w p z ∂((torusMeasure d).prod AddCircle.haarAddCircle)) =
      1 - p * (1 - w.mass) := by
  rw [integral_prod_symm _ (activatedDensity_integrable w p)]
  have hx (y : UnitAddCircle) :
      (∫ x, activatedDensity w p (x,y) ∂torusMeasure d) =
        1 - (activationSet p).indicator (fun _ => (1 : ℝ)) y * (1 - w.mass) := by
    by_cases hy : y ∈ activationSet p
    · simp [activatedDensity, hy, TorusWeight.mass]
    · simp [activatedDensity, hy]
  simp_rw [hx]
  rw [integral_sub (integrable_const _) ((integrable_const (1 : ℝ)).indicator
    (activationSet_measurable p) |>.mul_const _), integral_mul_const,
    activationSet_integral hp0 hp1]
  simp

end SchauderTranslates
