import Lean_Code.SchauderTranslates.Lp.HaarCoefficientMaps
import Lean_Code.SchauderTranslates.Lp.DyadicStepValues

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haarCoefficientMap_eq_of_ae {p q r u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ u)]
    [ENNReal.HolderConjugate p q] [ENNReal.HolderConjugate r u]
    (i : HaarIndex) (f : HaarLp p) (g : HaarLp r)
    (hfg : (f : ℝ → ℂ) =ᵐ[haarMeasure] g) :
    haarCoefficientMap p q i f = haarCoefficientMap r u i g := by
  rw [haarCoefficientMap_apply, haarCoefficientMap_apply]
  apply integral_congr_ae
  filter_upwards [hfg, haarAtom_ae_value p i, haarAtom_ae_value r i] with x hfg hp hr
  rw [hfg, hp, hr]

theorem haar_finite_combination_ae (p r : ℝ≥0∞) (t : Finset HaarIndex) (c : HaarIndex → ℂ) :
    ((∑ i ∈ t, c i • haarAtom p i : HaarLp p) : ℝ → ℂ) =ᵐ[haarMeasure]
      ((∑ i ∈ t, c i • haarAtom r i : HaarLp r) : ℝ → ℂ) := by
  have hall : ∀ᵐ x ∂haarMeasure, ∀ i ∈ t, (c i • haarAtom p i) x = (c i • haarAtom r i) x := by
    simp only [Filter.eventually_all_finset]
    intro i _
    filter_upwards [haarAtom_ae_value p i, haarAtom_ae_value r i,
      Lp.coeFn_smul (c i) (haarAtom p i), Lp.coeFn_smul (c i) (haarAtom r i)] with x hp hr hsp hsr
    rw [hsp, hsr, Pi.smul_apply, Pi.smul_apply, hp, hr]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum t (fun i => c i • haarAtom p i),
    Lp.coeFn_fun_finsetSum t (fun i => c i • haarAtom r i)] with x hall hp hr
  rw [hp, hr]
  exact Finset.sum_congr rfl (fun i hi => hall i hi)

/-- The finite integral formula describes the same measurable function
in different Lᵖ spaces whenever the inputs represent the same function. -/
theorem haarLpMultiplier_ae_of_ae {p q r u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ u)]
    [ENNReal.HolderConjugate p q] [ENNReal.HolderConjugate r u]
    (t : Finset HaarIndex) (w : HaarIndex → ℂ) (f : HaarLp p) (g : HaarLp r)
    (hfg : (f : ℝ → ℂ) =ᵐ[haarMeasure] g) :
    (haarLpMultiplier p q t w f : ℝ → ℂ) =ᵐ[haarMeasure] haarLpMultiplier r u t w g := by
  have he : (∑ i ∈ t, (w i * haarCoefficientMap r u i g) • haarAtom r i) =
      ∑ i ∈ t, (w i * haarCoefficientMap p q i f) • haarAtom r i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [haarCoefficientMap_eq_of_ae (q := q) (u := u) i f g hfg]
  rw [haarLpMultiplier_apply, haarLpMultiplier_apply, he]
  exact haar_finite_combination_ae p r t _

theorem haarLpMultiplier_dyadic_ae {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    (t : Finset HaarIndex) (w : HaarIndex → ℂ) :
    (haarLpMultiplier p q t w (haarDyadicStep p N c) : ℝ → ℂ) =ᵐ[haarMeasure]
      haarL2Multiplier t w (haarDyadicStep 2 N c) := by
  rw [← haarLpMultiplier_two]
  exact haarLpMultiplier_ae_of_ae t w _ _
    ((haarDyadicStep_ae_value p N c).trans (haarDyadicStep_ae_value 2 N c).symm)

end SchauderTranslates.LpConstruction
