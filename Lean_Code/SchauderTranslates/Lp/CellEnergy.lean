import Lean_Code.SchauderTranslates.Lp.LpRestriction
import Lean_Code.SchauderTranslates.Lp.RoundCatalogs

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α ι : Type*} [MeasurableSpace α]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- Disjoint measurable restrictions cannot use more pth-power norm than
the original Lᵖ class. The bound uses the actual restricted measures. -/
theorem lp_restriction_finite_power_le (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (s : Finset ι) (A : ι → Set α) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) (F : Lp ℂ p μ) :
    (∑ i ∈ s, ‖lpRestriction p μ (A i) F‖ ^ p.toReal) ≤ ‖F‖ ^ p.toReal := by
  have hF := integrable_norm_rpow F hp0 hpfin
  calc
    _ = ∑ i ∈ s, ∫ x in A i, ‖F x‖ ^ p.toReal ∂μ :=
      Finset.sum_congr rfl (fun i hi => lpRestriction_norm_rpow p μ (A i) hp0 hpfin F)
    _ = ∫ x in ⋃ i ∈ s, A i, ‖F x‖ ^ p.toReal ∂μ :=
      (integral_biUnion_finset s hA hdis (fun i hi => hF.integrableOn)).symm
    _ ≤ ∫ x, ‖F x‖ ^ p.toReal ∂μ :=
      setIntegral_le_integral hF (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    _ = ‖F‖ ^ p.toReal := integral_norm_rpow F hp0 hpfin

/-- Norm-one functionals on disjoint cells have an ℓᵖ energy bound. -/
theorem cell_functional_finite_power_le (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (s : Finset ι) (A : ι → Set α) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (φ : ∀ i, Lp ℂ p (μ.restrict (A i)) →L[ℂ] ℂ) (hφ : ∀ i ∈ s, ‖φ i‖ ≤ 1) (F : Lp ℂ p μ) :
    (∑ i ∈ s, ‖φ i (lpRestriction p μ (A i) F)‖ ^ p.toReal) ≤ ‖F‖ ^ p.toReal := by
  calc
    _ ≤ ∑ i ∈ s, ‖lpRestriction p μ (A i) F‖ ^ p.toReal := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.rpow_le_rpow (norm_nonneg _)
      · exact ((φ i).le_opNorm _).trans (by
          simpa using mul_le_mul_of_nonneg_right (hφ i hi) (norm_nonneg (lpRestriction p μ (A i) F)))
      · exact ENNReal.toReal_nonneg
    _ ≤ ‖F‖ ^ p.toReal := lp_restriction_finite_power_le hp0 hpfin s A hA hdis F

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

theorem globalCell_finite_power_le (s : Finset ℕ) (F : LebesgueLp p) :
    (∑ i ∈ s, ‖lpRestriction p volume (globalCell p q hp2 hpfin i).support F‖ ^ p.toReal) ≤ ‖F‖ ^ p.toReal := by
  apply lp_restriction_finite_power_le (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin
  · exact fun i _ => (globalCell p q hp2 hpfin i).support_measurable
  · exact fun i _ j _ hij => globalCell_pairwise_disjoint p q hp2 hpfin hij

end SchauderTranslates.LpConstruction
