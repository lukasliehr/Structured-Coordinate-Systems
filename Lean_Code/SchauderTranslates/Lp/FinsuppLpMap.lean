import Lean_Code.SchauderTranslates.Lp.PrivateCellCoordinates
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SchauderTranslates.LpConstruction

variable {ι : Type*} [DecidableEq ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Finite coefficients viewed in their actual ℓᵖ norm. No norm on the
Finsupp domain is used to estimate synthesis. -/
def finsuppLp : (ι →₀ ℂ) →ₗ[ℂ] lp (fun _ : ι => ℂ) p where
  toFun c := ⟨⇑c, (memℓp_zero_iff.mpr c.hasFiniteSupport).of_exponent_ge zero_le⟩
  map_add' _ _ := by apply lp.ext; funext i; rfl
  map_smul' _ _ := by apply lp.ext; funext i; rfl

theorem finsuppLp_apply (c : ι →₀ ℂ) (i : ι) : finsuppLp p c i = c i := rfl

theorem finsuppLp_single (i : ι) (a : ℂ) : finsuppLp p (Finsupp.single i a) = lp.single p i a := by
  apply lp.ext
  funext j
  change (Finsupp.single i a) j = (lp.single (E := fun _ : ι => ℂ) p i a) j
  by_cases h : j = i <;> simp [h]

theorem finsuppLp_eq_sum (c : ι →₀ ℂ) : finsuppLp p c = ∑ i ∈ c.support, lp.single p i (c i) := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  by_cases hj : j ∈ c.support
  · simp [hj, finsuppLp_apply]
  · simp [hj, Finsupp.notMem_support_iff.mp hj, finsuppLp_apply]

theorem finsuppLp_norm_rpow (hp : 0 < p.toReal) (c : ι →₀ ℂ) :
    ‖finsuppLp p c‖ ^ p.toReal = ∑ i ∈ c.support, ‖c i‖ ^ p.toReal := by
  rw [finsuppLp_eq_sum]
  exact lp.norm_sum_single hp c c.support

theorem finsuppLp_dense (hpfin : p ≠ ∞) : DenseRange (finsuppLp p : (ι →₀ ℂ) → lp (fun _ : ι => ℂ) p) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single hpfin x)
  apply Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, Finsupp.single i (x i), ?_⟩
  rw [map_sum]
  simp only [finsuppLp_single]

end SchauderTranslates.LpConstruction
