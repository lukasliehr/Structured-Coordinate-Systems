import Lean_Code.SchauderTranslates.ActivationMoments
import Lean_Code.SchauderTranslates.ScalarActivation
import Lean_Code.SchauderTranslates.CircleRowsTotal

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- The actual product-weight Gram coefficient equals the coefficient of the full operator. -/
theorem activatedGram_fourier_entry (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    inner ℂ (circleRow (EuclideanSpace.single i 1) k)
      (s.activatedGram p (circleRow (EuclideanSpace.single j 1) l)) =
        s.activatedMoment p i j k l := by
  rw [s.activatedMoment_fubini]
  exact circleRow_activation_inner s.rawGram p i j k l

/-- No other bounded operator has the product-weight Fourier Gram coefficients. -/
theorem activatedGram_unique (s : ScalarData d n) (p : ℝ)
    (G : ActivationSpace n →L[ℂ] ActivationSpace n)
    (hG : ∀ (i j : Unit ⊕ Fin n) (k l : ℤ),
      inner ℂ (circleRow (EuclideanSpace.single i 1) k)
        (G (circleRow (EuclideanSpace.single j 1) l)) = s.activatedMoment p i j k l) :
    G = s.activatedGram p := by
  apply circleRows_operator_ext
  intro i j k l
  rw [hG, s.activatedGram_fourier_entry]

end ScalarData

/-- Rare activation with its actual Fourier Gram, two-sided inverse, strict positivity,
upper energy bound, real Fourier entries, and exact unnormalized mass. -/
theorem rare_activation_gram {d n : ℕ} (s : ScalarData d n) (he : s.IsEven)
    (hfloor : s.HasPositiveFloor) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    MeasurableSet (activationSet p) ∧
    (∀ y, -y ∈ activationSet p ↔ y ∈ activationSet p) ∧
    AddCircle.haarAddCircle (activationSet p) = ENNReal.ofReal p ∧
    (∫ z, activatedDensity s.toTorusWeight p z
      ∂((torusMeasure d).prod AddCircle.haarAddCircle)) = 1 - p * (1 - s.mass) ∧
    (s.activatedGram p).comp (s.activatedInverse p) = 1 ∧
    (s.activatedInverse p).comp (s.activatedGram p) = 1 ∧
    (∀ f : ScalarData.ActivationSpace n, f ≠ 0 →
      0 < RCLike.re (inner ℂ (s.activatedGram p f) f)) ∧
    (∀ f : ScalarData.ActivationSpace n,
      RCLike.re (inner ℂ (s.activatedGram p f) f) ≤ ‖f‖ ^ 2) ∧
    (∀ (i j : Unit ⊕ Fin n) (k l : ℤ),
      inner ℂ (circleRow (EuclideanSpace.single i 1) k)
        (s.activatedGram p (circleRow (EuclideanSpace.single j 1) l)) =
          s.activatedMoment p i j k l) ∧
    (∀ (i j : Unit ⊕ Fin n) (k l : ℤ), (s.activatedMoment p i j k l).im = 0) := by
  refine ⟨activationSet_measurable p, activationSet_neg_mem p,
    activationSet_measure hp1.le, activatedDensity_mass s.toTorusWeight hp0.le hp1.le,
    (s.activatedGram_inverse p).1, (s.activatedGram_inverse p).2,
    s.activatedGram_strict hfloor p, ?_, s.activatedGram_fourier_entry p,
    s.activatedMoment_real he p⟩
  intro f
  exact (s.activatedGram_bounds (b := 0) le_rfl (fun x => (s.positive x).le) p f).2

end SchauderTranslates
