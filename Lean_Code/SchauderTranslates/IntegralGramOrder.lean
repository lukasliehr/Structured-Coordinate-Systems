import Lean_Code.SchauderTranslates.IntegralGram

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]

/-- Constant real weights rescale the reference Gram exactly. -/
theorem integralGram_const (v : ι → S → ℂ) (c : ℝ) :
    integralGram μ (fun _ => c) v = (c : ℂ) • integralGram μ (fun _ => 1) v := by
  ext i j
  simp only [integralGram, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, mul_assoc,
    integral_const_mul]

/-- Subtracting two bounded measurable densities subtracts their actual Grams. -/
theorem integralGram_sub {w u : S → ℝ} (hw : Measurable w) (hu : Measurable u) {C D : ℝ}
    (hC : ∀ x, |w x| ≤ C) (hD : ∀ x, |u x| ≤ D) {v : ι → S → ℂ}
    (hv : ∀ i, Measurable (v i)) (hb : ∀ i, ∃ B : ℝ, ∀ x, ‖v i x‖ ≤ B) :
    integralGram μ (fun x => w x - u x) v = integralGram μ w v - integralGram μ u v := by
  ext i j
  simp only [integralGram, Matrix.sub_apply, Complex.ofReal_sub, sub_mul]
  exact integral_sub (integralGram_integrand μ hw hC hv hb i j)
    (integralGram_integrand μ hu hD hv hb i j)

/-- A weight with a positive pointwise floor turns an orthonormal reference list into
an actual positive definite contraction Gram, retaining the explicit matrix floor. -/
theorem integralGram_positive_contraction [Fintype ι] [DecidableEq ι]
    {w : S → ℝ} (hw : Measurable w) {β : ℝ} (hβ : 0 < β)
    (hfloor : ∀ x, β ≤ w x) (hupper : ∀ x, w x ≤ 1)
    {v : ι → S → ℂ} (hv : ∀ i, Measurable (v i))
    (hb : ∀ i, ∃ B : ℝ, ∀ x, ‖v i x‖ ≤ B)
    (href : integralGram μ (fun _ => 1) v = 1) :
    (integralGram μ w v).PosDef ∧ (1 - integralGram μ w v).PosSemidef ∧
      (integralGram μ w v - (β : ℂ) • 1).PosSemidef := by
  have hw0 (x : S) : 0 ≤ w x := hβ.le.trans (hfloor x)
  have hwabs (x : S) : |w x| ≤ 1 := by rw [abs_of_nonneg (hw0 x)]; exact hupper x
  have hI : (1 - integralGram μ w v).PosSemidef := by
    have h := integralGram_posSemidef μ (w := fun x => 1 - w x) (measurable_const.sub hw)
      (fun x => sub_nonneg.mpr (hupper x))
      (C := 1) (fun x => by linarith [hw0 x]) hv hb
    rw [integralGram_sub μ measurable_const hw (fun _ => by norm_num : ∀ _ : S, |(1 : ℝ)| ≤ 1)
      hwabs hv hb, href] at h
    exact h
  have hF : (integralGram μ w v - (β : ℂ) • 1).PosSemidef := by
    have h := integralGram_posSemidef μ (w := fun x => w x - β) (hw.sub measurable_const)
      (fun x => sub_nonneg.mpr (hfloor x))
      (C := 1 - β) (fun x => by linarith [hupper x]) hv hb
    rw [integralGram_sub μ hw measurable_const hwabs (fun _ => le_rfl : ∀ _ : S, |β| ≤ |β|)
      hv hb, integralGram_const, href] at h
    exact h
  have hβI : ((β : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hβ)
  have hP := hβI.add_posSemidef hF
  simp only [add_sub_cancel] at hP
  exact ⟨hP, hI, hF⟩

end SchauderTranslates
