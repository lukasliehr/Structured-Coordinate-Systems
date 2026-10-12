import Lean_Code.SchauderTranslates.ActivationOperator
import Lean_Code.SchauderTranslates.ActivationSet
import Lean_Code.SchauderTranslates.ScalarOrder

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

abbrev ActivationSpace (n : ℕ) :=
  Lp (EuclideanSpace ℂ (Unit ⊕ Fin n)) 2 (AddCircle.haarAddCircle (T := 1))

/-- The full raw activated Gram on the old rows and all circle modes. -/
def activatedGram (s : ScalarData d n) (p : ℝ) : ActivationSpace n →L[ℂ] ActivationSpace n :=
  activationOperator (activationSet p) (activationSet_measurable p)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram)

/-- Candidate inverse, with the original raw inverse in the active block. -/
def activatedInverse (s : ScalarData d n) (p : ℝ) : ActivationSpace n →L[ℂ] ActivationSpace n :=
  activationOperator (activationSet p) (activationSet_measurable p)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹)

theorem activatedGram_inverse (s : ScalarData d n) (p : ℝ) :
    (s.activatedGram p).comp (s.activatedInverse p) = 1 ∧
    (s.activatedInverse p).comp (s.activatedGram p) = 1 := by
  apply activationOperator_inverse
  · change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram *
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp s.rawGram_posDef.isUnit), map_one]
  · change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹ *
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp s.rawGram_posDef.isUnit), map_one]

theorem activatedGram_symmetric (s : ScalarData d n) (p : ℝ)
    (f g : ActivationSpace n) :
    inner ℂ (s.activatedGram p f) g = inner ℂ f (s.activatedGram p g) := by
  apply activationOperator_symmetric
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr s.rawGram_posDef.isHermitian

/-- Coercivity and the upper bound use the exact Euclidean L² norm. -/
theorem activatedGram_bounds (s : ScalarData d n) {b : ℝ} (hb : 0 ≤ b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (f : ActivationSpace n) :
    b * ‖f‖ ^ 2 ≤ RCLike.re (inner ℂ (s.activatedGram p f) f) ∧
    RCLike.re (inner ℂ (s.activatedGram p f) f) ≤ ‖f‖ ^ 2 := by
  have hb1 : b ≤ 1 := (hfloor 0).trans (s.le_one 0)
  simpa only [one_mul, activatedGram] using! activationOperator_quadratic_bounds
    (activationSet p) (activationSet_measurable p)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram)
    hb1 (le_refl (1 : ℝ))
    (fun x => (s.rawGram_quadratic_bounds hb hfloor x).1)
    (fun x => by simpa only [one_mul] using (s.rawGram_quadratic_bounds hb hfloor x).2) f

/-- Every nonzero coefficient function has strictly positive raw energy. -/
theorem activatedGram_strict (s : ScalarData d n) (hfloor : s.HasPositiveFloor)
    (p : ℝ) (f : ActivationSpace n) (hf : f ≠ 0) :
    0 < RCLike.re (inner ℂ (s.activatedGram p f) f) := by
  obtain ⟨b, hb, hfloor⟩ := hfloor
  exact lt_of_lt_of_le (mul_pos hb (sq_pos_of_pos (norm_pos_iff.mpr hf)))
    (s.activatedGram_bounds hb.le hfloor p f).1

end ScalarData
end SchauderTranslates
