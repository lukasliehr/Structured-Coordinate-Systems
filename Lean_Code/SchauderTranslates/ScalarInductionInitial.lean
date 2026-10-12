import Lean_Code.SchauderTranslates.InitialScalar
import Lean_Code.SchauderTranslates.ScalarCopyPrefixBounds
import Lean_Code.SchauderTranslates.ScalarProductPrefixes
import Lean_Code.SchauderTranslates.ScalarFloor

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The initial scalar block in the same independent-copy representation used by every later stage.
There is exactly one copy, so its mass, gain and inverse diagonals retain the initial values. -/
def scalarInductionInitial : ScalarData 1 1 := initialScalar.product 1

@[simp] theorem scalarInductionInitial_mass : scalarInductionInitial.mass = 9 / 10 := by
  simp [scalarInductionInitial, ScalarData.product_mass, initialScalar_mass]

@[simp] theorem scalarInductionInitial_gain : scalarInductionInitial.gain = 1 / 323 := by
  simp [scalarInductionInitial, ScalarData.product_gain, initialScalar_gain]

theorem scalarInductionInitial_even : scalarInductionInitial.IsEven :=
  initialScalar.product_even initialScalar_even 1

theorem scalarInductionInitial_floor : scalarInductionInitial.HasPositiveFloor :=
  initialScalar.product_positiveFloor initialScalar_floor 1

theorem scalarInductionInitial_centered : scalarInductionInitial.CenteredPrefixSqBound 2 :=
  initialScalar.product_centered_prefix 1 (by norm_num)
    ((initialScalar_centered_prefix_iff 2).mpr (by norm_num))

theorem scalarInductionInitial_augmented :
    scalarInductionInitial.AugmentedPrefixSqBound (2 + 10 * (1 / 323)) := by
  have h := initialScalar.product_augmented_prefix 1 (by norm_num : (2 : ℝ) ≤ 2)
    (by norm_num) (by rw [initialScalar_gain]; norm_num)
    ((initialScalar_centered_prefix_iff 2).mpr (by norm_num))
  simpa only [scalarInductionInitial, initialScalar_gain] using h

/-- A coarse initial inverse norm already gives the required spectral floor. -/
theorem scalarInductionInitial_inverse_norm :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) scalarInductionInitial.rawGram⁻¹‖ ≤ (100 : ℝ) := by
  have h := initialScalar.product_rawInverse_norm_le 1 initialScalar_inverse_norm.le
  rw [initialScalar_mass, initialScalar_gain] at h
  exact h.trans (by norm_num)

theorem scalarInductionInitial_inverse_excess (i : Fin 1) :
    (scalarInductionInitial.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 = 37 / 323 := by
  have he := congrArg (fun B : Matrix (Fin 1) (Fin 1) ℂ => B 0 0)
    initialScalar.rawGram_inverse_nonconstant
  change initialScalar.rawGram⁻¹ (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) =
    initialScalar.rawCenteredGram⁻¹ 0 0 at he
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hp := initialScalar.product_inverse_nonconstant 1 (0 : Fin 1) (0 : Fin 1)
  change scalarInductionInitial.rawGram⁻¹ (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) = _ at hp
  rw [hp, ← he, initialScalar_mass]
  norm_num [initialScalar_inverse_diagonal]

end SchauderTranslates
