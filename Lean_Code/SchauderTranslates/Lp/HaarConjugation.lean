import Lean_Code.SchauderTranslates.Lp.HaarPairing

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def haarConjugate {p : ℝ≥0∞} (f : HaarLp p) : HaarLp p :=
  (Lp.memLp f).star.toLp _

theorem haarConjugate_ae {p : ℝ≥0∞} (f : HaarLp p) :
    haarConjugate f =ᵐ[haarMeasure] fun x => star (f x) := MemLp.coeFn_toLp _

theorem haarConjugate_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : HaarLp p) :
    ‖haarConjugate f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (haarConjugate_ae f)]
  exact congrArg ENNReal.toReal eLpNorm_star

theorem haar_finite_combination_ae_value (p : ℝ≥0∞) (t : Finset HaarIndex)
    (c : HaarIndex → ℂ) :
    ((∑ i ∈ t, c i • haarAtom p i : HaarLp p) : ℝ → ℂ) =ᵐ[haarMeasure]
      fun x => ∑ i ∈ t, c i * haarValue i x := by
  have hall : ∀ᵐ x ∂haarMeasure, ∀ i ∈ t,
      (c i • haarAtom p i) x = c i * haarValue i x := by
    simp only [Filter.eventually_all_finset]
    intro i _
    filter_upwards [haarAtom_ae_value p i, Lp.coeFn_smul (c i) (haarAtom p i)] with x hi hs
    rw [hs, Pi.smul_apply, hi, smul_eq_mul]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum t (fun i => c i • haarAtom p i)] with x hall hx
  rw [hx]
  exact Finset.sum_congr rfl (fun i hi => hall i hi)

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haarCoefficientMap_conjugate (i : HaarIndex) (f : HaarLp p) :
    haarCoefficientMap p q i (haarConjugate f) = star (haarCoefficientMap p q i f) := by
  rw [haarCoefficientMap_apply, haarCoefficientMap_apply]
  have hc : star (∫ x, f x * star (haarAtom p i x) ∂haarMeasure) =
      ∫ x, star (f x * star (haarAtom p i x)) ∂haarMeasure := by
    simpa only [Complex.star_def] using
      (integral_conj (f := fun x => f x * star (haarAtom p i x)) (μ := haarMeasure)).symm
  rw [hc]
  apply integral_congr_ae
  filter_upwards [haarConjugate_ae f, haarAtom_ae_value p i] with x hx hi
  rw [hx, hi, star_haarValue, star_mul, star_haarValue]
  ring

theorem haarMultiplier_conjugate_ae (t : Finset HaarIndex) (w : HaarIndex → ℂ)
    (f : HaarLp p) :
    haarLpMultiplier p q t w (haarConjugate f) =ᵐ[haarMeasure]
      fun x => star (haarLpMultiplier p q t (fun i => star (w i)) f x) := by
  classical
  rw [haarLpMultiplier_apply, haarLpMultiplier_apply]
  have hleft := haar_finite_combination_ae_value p t
    (fun i => w i * haarCoefficientMap p q i (haarConjugate f))
  have hright := haar_finite_combination_ae_value p t
    (fun i => star (w i) * haarCoefficientMap p q i f)
  filter_upwards [hleft, hright] with x hl hr
  rw [hl, hr, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [haarCoefficientMap_conjugate (q := q),
    star_mul, star_mul, star_star, star_haarValue]
  ring

/-- The sesquilinear adjoint identity has conjugate multiplier
coefficients, exactly as in the paper's first-entry-linear convention. -/
theorem haar_multiplier_integral_adjoint (t : Finset HaarIndex) (w : HaarIndex → ℂ)
    (f : HaarLp p) (g : HaarLp q) :
    (∫ x, haarLpMultiplier p q t w f x * star (g x) ∂haarMeasure) =
      ∫ x, f x * star (haarLpMultiplier q p t (fun i => star (w i)) g x) ∂haarMeasure := by
  calc
    _ = haarPairing p q (haarLpMultiplier p q t w f) (haarConjugate g) := by
      rw [haarPairing_apply]
      apply integral_congr_ae
      filter_upwards [haarConjugate_ae g] with x hx
      rw [hx]
    _ = haarPairing p q f (haarLpMultiplier q p t w (haarConjugate g)) :=
      haar_multiplier_pairing_transpose p q t w f (haarConjugate g)
    _ = _ := by
      rw [haarPairing_apply]
      apply integral_congr_ae
      filter_upwards [haarMultiplier_conjugate_ae (q := p) t w g] with x hx
      rw [hx]

end SchauderTranslates.LpConstruction
