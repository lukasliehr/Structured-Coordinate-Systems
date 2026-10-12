import Lean_Code.SchauderTranslates.Lp.DyadicDecomposition

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem dyadicGoodPart_cell_norm_integral_le (f : ℝ → ℂ) (s : Finset DyadicCell)
    (hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet)
    {j : DyadicCell} (hj : j ∈ s) :
    (∫ x in dyadicCellSet j, ‖dyadicGoodPart f s x‖ ∂haarMeasure) ≤
      ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure := by
  calc
    _ = haarMeasure.real (dyadicCellSet j) * ‖dyadicCellMean f j‖ := by
      rw [setIntegral_congr_fun (dyadicCellSet_measurable j)
        (fun _ hx => congrArg norm (dyadicGoodPart_on_cell f s hd hj hx)),
        setIntegral_const, smul_eq_mul]
    _ ≤ haarMeasure.real (dyadicCellSet j) *
        ((haarMeasure.real (dyadicCellSet j))⁻¹ *
          ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure) :=
      mul_le_mul_of_nonneg_left (norm_dyadicCellMean_le f j) (dyadicCell_mass_pos j).le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ (dyadicCell_mass_pos j).ne', one_mul]

/-- Replacing each selected cell by its complex average decreases the
L¹ norm. This holds for every finite disjoint dyadic collection. -/
theorem dyadicGoodPart_norm_integral_le (f : ℝ → ℂ) (hf : Integrable f haarMeasure)
    (s : Finset DyadicCell) (hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet) :
    (∫ x, ‖dyadicGoodPart f s x‖ ∂haarMeasure) ≤ ∫ x, ‖f x‖ ∂haarMeasure := by
  let Ω := ⋃ j ∈ s, dyadicCellSet j
  have hΩ : MeasurableSet Ω := Finset.measurableSet_biUnion _ (fun j _ => dyadicCellSet_measurable j)
  have hg := dyadicGoodPart_integrable f hf s
  have houtside : (∫ x in Ωᶜ, ‖dyadicGoodPart f s x‖ ∂haarMeasure) =
      ∫ x in Ωᶜ, ‖f x‖ ∂haarMeasure :=
    setIntegral_congr_fun hΩ.compl (fun _ hx => congrArg norm (dyadicGoodPart_outside f s hx))
  rw [← integral_add_compl hΩ hg.norm, ← integral_add_compl hΩ hf.norm, houtside]
  refine add_le_add ?_ le_rfl
  change (∫ x in ⋃ j ∈ s, dyadicCellSet j, ‖dyadicGoodPart f s x‖ ∂haarMeasure) ≤
    ∫ x in ⋃ j ∈ s, dyadicCellSet j, ‖f x‖ ∂haarMeasure
  rw [integral_biUnion_finset s (fun j _ => dyadicCellSet_measurable j) hd
    (fun _ _ => hg.norm.integrableOn),
    integral_biUnion_finset s (fun j _ => dyadicCellSet_measurable j) hd
      (fun _ _ => hf.norm.integrableOn)]
  exact Finset.sum_le_sum fun j hj => dyadicGoodPart_cell_norm_integral_le f s hd hj

theorem integral_norm_square_le_of_bound (g : ℝ → ℂ) (hg : Integrable g haarMeasure)
    (hg2 : MemLp g 2 haarMeasure) {C : ℝ} (hbound : ∀ x, ‖g x‖ ≤ C) :
    (∫ x, ‖g x‖ ^ 2 ∂haarMeasure) ≤ C * ∫ x, ‖g x‖ ∂haarMeasure := by
  have hsq : Integrable (fun x => ‖g x‖ ^ 2) haarMeasure := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      memLp_one_iff_integrable.mp (hg2.norm_rpow (by norm_num) (by norm_num))
  rw [← integral_const_mul]
  apply integral_mono hsq (hg.norm.const_mul C)
  intro x
  simpa only [pow_two, mul_comm] using mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (g x))

/-- The good part's squared L² norm is bounded by 2a times the original
L¹ norm, in the exact form needed for Chebyshev and the L² contraction. -/
theorem dyadicGoodPart_square_integral_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    {a : ℝ} (ha : 0 ≤ a) (hf : (∫ x, ‖dyadicStepValue N c x‖ ∂haarMeasure) ≤ a) :
    (∫ x, ‖dyadicGoodPart (dyadicStepValue N c)
        (maximalDyadicCells (dyadicBadCells N (dyadicStepValue N c) a)) x‖ ^ 2 ∂haarMeasure) ≤
      2 * a * ∫ x, ‖dyadicStepValue N c x‖ ∂haarMeasure := by
  let f := dyadicStepValue N c
  let s := maximalDyadicCells (dyadicBadCells N f a)
  have hfi := dyadicStepValue_integrable N c
  have hbound := dyadicGoodPart_bound N c ha hf
  calc
    _ ≤ (2 * a) * ∫ x, ‖dyadicGoodPart f s x‖ ∂haarMeasure :=
      integral_norm_square_le_of_bound _ (dyadicGoodPart_integrable f hfi s)
        (dyadicGoodPart_memLp 2 f (dyadicStepValue_memLp 2 N c) s) hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadicGoodPart_norm_integral_le f hfi s
      (fun _ hi _ hj hij => maximalDyadicCells_disjoint _ hi hj hij)) (by positivity)

end SchauderTranslates.LpConstruction
