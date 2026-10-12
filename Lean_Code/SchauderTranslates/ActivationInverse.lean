import Lean_Code.SchauderTranslates.RareActivation
import Lean_Code.SchauderTranslates.InverseCompression

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace SchauderTranslates

/-- A circle Fourier character has unit absolute value also in the indicator block. -/
theorem circleRow_activation_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) (k : ℤ) :
    inner ℂ (circleRow (EuclideanSpace.single i 1) k)
      (activationOperator (activationSet p) (activationSet_measurable p)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B)
        (circleRow (EuclideanSpace.single i 1) k)) = 1 + (p : ℂ) * (B i i - 1) := by
  rw [circleRow_activation_inner]
  have he (y : UnitAddCircle) :
      (if y ∈ activationSet p then B i i else if i = i then 1 else 0) *
        star (fourier k y) * fourier k y =
      1 + (activationSet p).indicator (fun _ => B i i - 1) y := by
    have hk : star (fourier k y) * fourier k y = 1 := by
      simp [Complex.conj_mul', fourier_apply]
    rw [mul_assoc, hk, mul_one]
    by_cases hy : y ∈ activationSet p
    · simp only [hy, if_true, Set.indicator_of_mem hy]
      ring
    · simp only [hy, if_false, Set.indicator_of_notMem hy, if_true, add_zero]
  change (∫ y : UnitAddCircle,
    (if y ∈ activationSet p then B i i else if i = i then (1 : ℂ) else 0) *
      star (fourier k y) * fourier k y ∂AddCircle.haarAddCircle) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall he)]
  rw [integral_add (integrable_const _) ((integrable_const _).indicator (activationSet_measurable p)),
    integral_indicator_const (e := B i i - 1) (activationSet_measurable p)]
  simp [measureReal_def, activationSet_measure hp1, ENNReal.toReal_ofReal hp0, Complex.real_smul]

namespace ScalarData
variable {d n : ℕ}

/-- Each full inverse diagonal is the same in every Fourier mode of an old row. -/
theorem activatedInverse_diagonal (s : ScalarData d n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Unit ⊕ Fin n) (k : ℤ) :
    inner ℂ (circleRow (EuclideanSpace.single i 1) k)
      (s.activatedInverse p (circleRow (EuclideanSpace.single i 1) k)) =
        1 + (p : ℂ) * (s.rawGram⁻¹ i i - 1) :=
  circleRow_activation_diagonal s.rawGram⁻¹ hp0 hp1 i k

/-- Identifies the general coercive inverse used by compression with the explicit activation inverse. -/
theorem activated_coercive_inverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (f : ActivationSpace n) :
    (coerciveEquiv (s.activatedGram p) hb
      (fun x => (s.activatedGram_bounds hb.le hfloor p x).1)).symm f = s.activatedInverse p f := by
  apply (coerciveEquiv (s.activatedGram p) hb
    (fun x => (s.activatedGram_bounds hb.le hfloor p x).1)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change f = s.activatedGram p (s.activatedInverse p f)
  have he := congrArg (fun T : ActivationSpace n →L[ℂ] ActivationSpace n => T f)
    (s.activatedGram_inverse p).1
  exact he.symm

/-- The full constant inverse diagonal gives the limiting unnormalized cutoff gain. -/
def activationLimitGain (s : ScalarData d n) (p : ℝ) : ℝ :=
  (1 - p * (1 - s.mass)) * (1 + p * ((s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re - 1)) - 1

/-- Exact formula (S1), in terms of the old mass deficit and gain. -/
theorem activationLimitGain_formula (s : ScalarData d n) (p : ℝ) :
    s.activationLimitGain p =
      p / s.mass * (s.gain + (1 - s.mass) ^ 2 -
        p * (1 - s.mass) * (s.gain + (1 - s.mass))) := by
  unfold activationLimitGain
  rw [s.rawGram_inverse_constant_gain, Complex.ofReal_re]
  field_simp [s.mass_pos.ne']
  ring

end ScalarData
end SchauderTranslates
