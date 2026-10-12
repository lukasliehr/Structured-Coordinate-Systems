import Lean_Code.SchauderTranslates.ScalarGram
import Lean_Code.SchauderTranslates.MetricColumns

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- The Riesz vector of the scalar mean functional in centered Hilbert coordinates. -/
def meanRiesz (s : ScalarData d n) : EuclideanSpace ℂ (Fin n) :=
  gramRootInv s.centeredGram (WithLp.toLp 2 s.mean)

def meanFunctional (s : ScalarData d n) : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  innerSL ℂ s.meanRiesz

/-- Its squared norm is exactly the normalized scalar gain. -/
theorem meanRiesz_norm_sq (s : ScalarData d n) : ‖s.meanRiesz‖ ^ 2 = s.gain := by
  rw [meanRiesz, gramRootInv_eq_root_inverse s.centeredGram_posDef.posSemidef,
    gramRoot_norm_sq s.centeredGram_posDef.inv.posSemidef]
  change coefficientQuadratic s.centeredGram⁻¹ (WithLp.toLp 2 s.mean) = s.gain
  rw [coefficientQuadratic_eq_dot]
  rfl

theorem meanFunctional_norm_sq (s : ScalarData d n) : ‖s.meanFunctional‖ ^ 2 = s.gain := by
  rw [meanFunctional, innerSL_apply_norm, s.meanRiesz_norm_sq]

/-- Evaluation on a centered primal column returns the actual (conjugated-column) mean. -/
theorem meanFunctional_column (s : ScalarData d n) (i : Fin n) :
    s.meanFunctional (metricColumn s.centeredGram i) = star (s.mean i) := by
  change inner ℂ (gramRootInv s.centeredGram (WithLp.toLp 2 s.mean))
    (gramRoot s.centeredGram (EuclideanSpace.single i 1)) = _
  rw [← adjoint_inner_right, gramRootInv_adjoint s.centeredGram_posDef.posSemidef,
    ← ContinuousLinearMap.comp_apply, gramRoot_inv_mul s.centeredGram_posDef, one_apply_eq_self,
    EuclideanSpace.inner_single_right]
  simp

/-- Normalized constant-plus-centered coordinates of the augmented scalar family. -/
def hilbertModel (s : ScalarData d n) : Unit ⊕ Fin n → WithLp 2 (ℂ × EuclideanSpace ℂ (Fin n)) :=
  Sum.elim (fun _ => WithLp.toLp 2 (1, 0))
    (fun i => WithLp.toLp 2 (star (s.mean i), metricColumn s.centeredGram i))

/-- The concrete Hilbert model represents the full normalized Gram, not only its centered part. -/
theorem hilbertModel_gram (s : ScalarData d n) :
    Matrix.gram ℂ s.hilbertModel = (s.mass : ℂ)⁻¹ • s.rawGram := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  ext (i | i) (j | j)
  · cases i; cases j
    simp [Matrix.gram_apply, hilbertModel, WithLp.prod_inner_apply, s.rawGram_diagonal, hm]
  · cases i
    have hraw : s.rawGram (Sum.inl ()) (Sum.inr j) = star (s.moment j) :=
      (s.rawGram_posDef.isHermitian.apply _ _).symm
    simp [Matrix.gram_apply, hilbertModel, WithLp.prod_inner_apply, hraw, mean,
      Complex.star_def, Complex.conj_ofReal]
  · cases j
    simp [Matrix.gram_apply, hilbertModel, WithLp.prod_inner_apply, mean, moment]
  · change inner ℂ (star (s.mean i)) (star (s.mean j)) +
      inner ℂ (metricColumn s.centeredGram i) (metricColumn s.centeredGram j) =
        (s.mass : ℂ)⁻¹ * s.rawGram (Sum.inr i) (Sum.inr j)
    rw [metricColumn_inner s.centeredGram_posDef.posSemidef]
    simp only [RCLike.inner_apply, star_star, mean, Pi.smul_apply, smul_eq_mul, map_mul,
      map_inv₀, Complex.star_def, Complex.conj_ofReal, centeredGram, rawCenteredGram,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    simp only [Complex.conj_conj]
    change _ = (s.mass : ℂ)⁻¹ * s.nonconstantGram i j
    ring

end ScalarData
end SchauderTranslates
