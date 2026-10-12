import Lean_Code.SchauderTranslates.Lp.HaarDual

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haarCoefficientMap_atom (i j : HaarIndex) :
    haarCoefficientMap p q i (haarAtom p j) = if i = j then 1 else 0 := by
  calc
    _ = haarCoefficientMap 2 2 i (haarAtom 2 j) :=
      haarCoefficientMap_eq_of_ae (q := q) (u := 2) i _ _
        ((haarAtom_ae_value p j).trans (haarAtom_ae_value 2 j).symm)
    _ = inner ℂ (haarAtom 2 i) (haarAtom 2 j) := by
      rw [haarCoefficientMap_apply, haar_l2_coefficient_integral]
    _ = _ := (orthonormal_iff_ite.mp haar_orthonormal) i j

theorem haarAtom_ne_zero (i : HaarIndex) : haarAtom p i ≠ 0 := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro h
  have hc := haarCoefficientMap_atom p (ENNReal.conjExponent p) i i
  simp [h] at hc

def haarNormalizedAtom (i : HaarIndex) : HaarLp p :=
  (‖haarAtom p i‖⁻¹ : ℂ) • haarAtom p i

def haarNormalizedCoordinate (i : HaarIndex) : HaarLp p →L[ℂ] ℂ :=
  (‖haarAtom p i‖ : ℂ) • haarCoefficientMap p q i

theorem haarNormalizedAtom_norm (i : HaarIndex) : ‖haarNormalizedAtom p i‖ = 1 := by
  have hn : ‖haarAtom p i‖ ≠ 0 := norm_ne_zero_iff.mpr (haarAtom_ne_zero p i)
  rw [haarNormalizedAtom, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

theorem haarNormalizedCoordinate_atom (i j : HaarIndex) :
    haarNormalizedCoordinate p q i (haarNormalizedAtom p j) = if i = j then 1 else 0 := by
  classical
  rw [haarNormalizedCoordinate, smul_apply, haarNormalizedAtom,
    map_smul, haarCoefficientMap_atom, smul_eq_mul, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [haarAtom_ne_zero p i]
  · simp [hij]

theorem haar_normalization_coordinate_term (i : HaarIndex) (f : HaarLp p) :
    haarNormalizedCoordinate p q i f • haarNormalizedAtom p i =
      haarCoefficientMap p q i f • haarAtom p i := by
  have hn : (‖haarAtom p i‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (haarAtom_ne_zero p i))
  rw [haarNormalizedCoordinate, smul_apply, haarNormalizedAtom,
    smul_eq_mul, smul_smul]
  congr 1
  rw [mul_right_comm, mul_inv_cancel₀ hn, one_mul]

def haarNormalizedMultiplier (t : Finset HaarIndex) (w : HaarIndex → ℂ) :
    HaarLp p →L[ℂ] HaarLp p :=
  ∑ i ∈ t, w i • (haarNormalizedCoordinate p q i).smulRight (haarNormalizedAtom p i)

theorem haarNormalizedMultiplier_eq (t : Finset HaarIndex) (w : HaarIndex → ℂ) :
    haarNormalizedMultiplier p q t w = haarLpMultiplier p q t w := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [haarNormalizedMultiplier, haarLpMultiplier, sum_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v => w i • v)
    (haar_normalization_coordinate_term p q i f))

theorem haarStrongConstant_ge_one {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    1 ≤ haarStrongConstant q.toReal := by
  have hb := haar_dual_multiplier_bound (q := q) hp2 hpfin {none} (fun _ => 1)
    (by simp) (haarAtom p none)
  rw [haarLpMultiplier_apply] at hb
  simp only [Finset.sum_singleton, one_mul, haarCoefficientMap_atom, ite_true, one_smul] at hb
  change ‖haarConstant p‖ ≤ haarStrongConstant q.toReal * ‖haarConstant p‖ at hb
  simpa only [norm_haarConstant p (ENNReal.HolderConjugate.ne_zero p q) hpfin, mul_one] using hb

end SchauderTranslates.LpConstruction
