import Lean_Code.SchauderTranslates.Lp.HaarStrong

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def haarPairing : HaarLp p →L[ℂ] HaarLp q →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing haarMeasure p q

theorem haarPairing_apply (f : HaarLp p) (g : HaarLp q) :
    haarPairing p q f g = ∫ x, f x * g x ∂haarMeasure :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f g

theorem haarPairing_norm_le (f : HaarLp p) (g : HaarLp q) :
    ‖haarPairing p q f g‖ ≤ ‖f‖ * ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have he : haarPairing p q f g = L1.integral (B.holder 1 f g) := by
    rw [haarPairing_apply, L1.integral_eq_integral]
    exact (integral_congr_ae (B.coeFn_holder f g)).symm
  calc
    _ = ‖L1.integral (B.holder 1 f g)‖ := by rw [he]
    _ ≤ ‖B.holder 1 f g‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖g‖ := B.norm_holder_apply_apply_le f g
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
    _ = _ := by ring

theorem haarPairing_atom_left (i : HaarIndex) (g : HaarLp q) :
    haarPairing p q (haarAtom p i) g = haarCoefficientMap q p i g := by
  rw [haarPairing_apply, haarCoefficientMap_apply]
  apply integral_congr_ae
  filter_upwards [haarAtom_ae_value p i, haarAtom_ae_value q i] with x hp hq
  rw [hp, hq, star_haarValue, mul_comm]

theorem haarPairing_atom_right (i : HaarIndex) (f : HaarLp p) :
    haarPairing p q f (haarAtom q i) = haarCoefficientMap p q i f := by
  rw [haarPairing_apply, haarCoefficientMap_apply]
  apply integral_congr_ae
  filter_upwards [haarAtom_ae_value p i, haarAtom_ae_value q i] with x hp hq
  rw [hp, hq, star_haarValue]

/-- The bilinear transpose has the same coefficients. Complex-conjugate
adjoint coefficients follow by conjugating the second input. -/
theorem haar_multiplier_pairing_transpose (t : Finset HaarIndex) (w : HaarIndex → ℂ)
    (f : HaarLp p) (g : HaarLp q) :
    haarPairing p q (haarLpMultiplier p q t w f) g =
      haarPairing p q f (haarLpMultiplier q p t w g) := by
  have hleft : haarPairing p q (haarLpMultiplier p q t w f) g =
      ∑ i ∈ t, (w i * haarCoefficientMap p q i f) * haarCoefficientMap q p i g := by
    change (haarPairing p q).flip g (haarLpMultiplier p q t w f) = _
    rw [haarLpMultiplier_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, ContinuousLinearMap.flip_apply, haarPairing_atom_left]
  have hright : haarPairing p q f (haarLpMultiplier q p t w g) =
      ∑ i ∈ t, (w i * haarCoefficientMap q p i g) * haarCoefficientMap p q i f := by
    rw [haarLpMultiplier_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, haarPairing_atom_right]
  rw [hleft, hright]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end SchauderTranslates.LpConstruction
