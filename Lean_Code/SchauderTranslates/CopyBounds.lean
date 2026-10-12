import Lean_Code.SchauderTranslates.RowSplit

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Weighted Young's inequality in the form needed for a triangular Hilbert block. -/
theorem weighted_square_bound {δ : ℝ} (hδ : 0 < δ) (a b r s : ℝ) :
    (a * r + b * s) ^ 2 ≤ (a ^ 2 + δ) * (r ^ 2 + b ^ 2 / δ * s ^ 2) := by
  have hid : δ * ((a ^ 2 + δ) * (r ^ 2 + b ^ 2 / δ * s ^ 2) -
      (a * r + b * s) ^ 2) = (δ * r - a * b * s) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (a ^ 2 + δ) * (r ^ 2 + b ^ 2 / δ * s ^ 2) -
      (a * r + b * s) ^ 2 := (mul_nonneg_iff_of_pos_left hδ).mp (by rw [hid]; positivity)
  linarith

/-- The same numerical margin works at eta = 0, with no division by eta. -/
theorem triangular_scalar_bound {q Z η a b r s : ℝ}
    (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hq : 1 + Z < q)
    (ha : a ^ 2 ≤ 1 + Z) (hb : b ^ 2 ≤ q * η) :
    (a * r + b * s) ^ 2 + q * s ^ 2 ≤
      (q + q ^ 2 * η / (q - 1 - Z)) * (r ^ 2 + s ^ 2) := by
  have hδ : 0 < q - 1 - Z := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hd : 0 ≤ q ^ 2 * η / (q - 1 - Z) := by positivity
  have hbase : 0 ≤ r ^ 2 + b ^ 2 / (q - 1 - Z) * s ^ 2 := by positivity
  calc
    _ ≤ (a ^ 2 + (q - 1 - Z)) * (r ^ 2 + b ^ 2 / (q - 1 - Z) * s ^ 2) + q * s ^ 2 :=
      by linarith [weighted_square_bound hδ a b r s]
    _ ≤ q * (r ^ 2 + b ^ 2 / (q - 1 - Z) * s ^ 2) + q * s ^ 2 := by
      gcongr
      linarith
    _ ≤ q * (r ^ 2 + (q * η) / (q - 1 - Z) * s ^ 2) + q * s ^ 2 := by gcongr
    _ = q * r ^ 2 + (q + q ^ 2 * η / (q - 1 - Z)) * s ^ 2 := by ring
    _ ≤ _ := by nlinarith [mul_nonneg hd (sq_nonneg r)]

section Triangular
variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The nontrivial block of a cut inside one lifted copy. -/
def hilbertTriangular (A : E →L[𝕜] F) (U : G →L[𝕜] F) (P : G →L[𝕜] H) :
    WithLp 2 (E × G) →L[𝕜] WithLp 2 (F × H) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 F H).symm.toContinuousLinearMap.comp
    ((A.comp (WithLp.fstL 2 𝕜 E G) - U.comp (WithLp.sndL 2 𝕜 E G)).prod
      (P.comp (WithLp.sndL 2 𝕜 E G)))

@[simp] theorem hilbertTriangular_apply (A : E →L[𝕜] F) (U : G →L[𝕜] F)
    (P : G →L[𝕜] H) (z : WithLp 2 (E × G)) :
    hilbertTriangular A U P z = WithLp.toLp 2 (A z.fst - U z.snd, P z.snd) := rfl

/-- The quantitative triangular block estimate used for concatenation. -/
theorem hilbertTriangular_norm_sq_le (A : E →L[𝕜] F) (U : G →L[𝕜] F) (P : G →L[𝕜] H)
    {q Z η : ℝ} (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hq : 1 + Z < q)
    (hA : ‖A‖ ^ 2 ≤ 1 + Z) (hU : ‖U‖ ^ 2 ≤ q * η) (hP : ‖P‖ ^ 2 ≤ q) :
    ‖hilbertTriangular A U P‖ ^ 2 ≤ q + q ^ 2 * η / (q - 1 - Z) := by
  have hδ : 0 < q - 1 - Z := by linarith
  have hq0 : 0 ≤ q := by linarith
  apply opNorm_sq_le_of_pointwise _ (by positivity)
  intro z
  rw [hilbertTriangular_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖A z.fst - U z.snd‖ ^ 2 + ‖P z.snd‖ ^ 2 ≤ _
  have hup : ‖A z.fst - U z.snd‖ ≤ ‖A‖ * ‖z.fst‖ + ‖U‖ * ‖z.snd‖ :=
    (norm_sub_le _ _).trans (add_le_add (A.le_opNorm _) (U.le_opNorm _))
  have hs := pow_le_pow_left₀ (norm_nonneg (A z.fst - U z.snd)) hup 2
  have hp := pow_le_pow_left₀ (norm_nonneg (P z.snd)) (P.le_opNorm z.snd) 2
  have hpn := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖z.snd‖)
  have hb := triangular_scalar_bound (r := ‖z.fst‖) (s := ‖z.snd‖) hZ hη hq hA hU
  nlinarith

end Triangular
end SchauderTranslates
