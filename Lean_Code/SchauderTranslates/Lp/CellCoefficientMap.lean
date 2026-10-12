import Lean_Code.SchauderTranslates.Lp.CellEnergy

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α ι : Type*} [MeasurableSpace α]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (φ : ∀ i, Lp ℂ p (μ.restrict (A i)) →L[ℂ] ℂ) (hφ : ∀ i, ‖φ i‖ ≤ 1)

def cellCoefficientLinear : Lp ℂ p μ →ₗ[ℂ] lp (fun _ : ι => ℂ) p where
  toFun F := ⟨fun i => φ i (lpRestriction p μ (A i) F),
    memℓp_gen' (fun s => cell_functional_finite_power_le hp0 hpfin s A
      (fun i _ => hA i) (fun i _ j _ hij => hdis hij) φ (fun i _ => hφ i) F)⟩
  map_add' F G := by
    apply lp.ext
    funext i
    change φ i (lpRestriction p μ (A i) (F + G)) =
      φ i (lpRestriction p μ (A i) F) + φ i (lpRestriction p μ (A i) G)
    rw [map_add, map_add]
  map_smul' a F := by
    apply lp.ext
    funext i
    change φ i (lpRestriction p μ (A i) (a • F)) = a • φ i (lpRestriction p μ (A i) F)
    rw [map_smul, map_smul]

theorem cellCoefficientLinear_bound (F : Lp ℂ p μ) :
    ‖cellCoefficientLinear hp0 hpfin A hA hdis φ hφ F‖ ≤ ‖F‖ := by
  apply lp.norm_le_of_forall_sum_le (ENNReal.toReal_pos hp0 hpfin) (norm_nonneg F)
  exact fun s => cell_functional_finite_power_le hp0 hpfin s A
    (fun i _ => hA i) (fun i _ j _ hij => hdis hij) φ (fun i _ => hφ i) F

/-- Continuous private-coordinate extraction obtained from the actual
disjoint-cell norm estimate. No coordinate summability is assumed. -/
def cellCoefficients : Lp ℂ p μ →L[ℂ] lp (fun _ : ι => ℂ) p :=
  (cellCoefficientLinear hp0 hpfin A hA hdis φ hφ).mkContinuous 1
    (fun F => by simpa using cellCoefficientLinear_bound hp0 hpfin A hA hdis φ hφ F)

theorem cellCoefficients_apply (F : Lp ℂ p μ) (i : ι) :
    cellCoefficients hp0 hpfin A hA hdis φ hφ F i = φ i (lpRestriction p μ (A i) F) := rfl

theorem cellCoefficients_norm_le : ‖cellCoefficients hp0 hpfin A hA hdis φ hφ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end SchauderTranslates.LpConstruction
