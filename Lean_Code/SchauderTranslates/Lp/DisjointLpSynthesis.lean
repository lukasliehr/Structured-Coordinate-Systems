import Lean_Code.SchauderTranslates.Lp.FinsuppLpMap

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {ι : Type*} [DecidableEq ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (e : ι → LebesgueLp p) (he : ∀ i, ‖e i‖ = 1)
    (hdis : Pairwise (fun i j => ∀ᵐ x ∂volume, e i x = 0 ∨ e j x = 0))

include hp0 hpfin he hdis

theorem disjoint_finite_synthesis_norm (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ e c‖ = ‖finsuppLp p c‖ := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hpR.ne').mp
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    norm_finset_sum_rpow c.support (fun i => c i • e i) hp0 hpfin,
    finsuppLp_norm_rpow p hpR]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [norm_smul, he i, mul_one]
  · intro i hi j hj hij
    filter_upwards [hdis hij, Lp.coeFn_smul (c i) (e i), Lp.coeFn_smul (c j) (e j)]
      with x hx hix hjx
    rcases hx with hx | hx
    · left
      rw [hix]
      change c i • e i x = 0
      rw [hx, smul_zero]
    · right
      rw [hjx]
      change c j • e j x = 0
      rw [hx, smul_zero]

/-- Synthesis of arbitrary ℓᵖ coefficients in disjoint unit coordinates,
obtained from finite coefficients by density in the actual ℓᵖ norm. -/
def disjointLpSynthesis : lp (fun _ : ι => ℂ) p →L[ℂ] LebesgueLp p :=
  (Finsupp.linearCombination ℂ e).extendOfNorm (finsuppLp p)

theorem disjointLpSynthesis_finite (c : ι →₀ ℂ) :
    disjointLpSynthesis e (finsuppLp p c) = Finsupp.linearCombination ℂ e c := by
  apply LinearMap.extendOfNorm_eq (finsuppLp_dense p hpfin)
  refine ⟨1, fun c => ?_⟩
  rw [one_mul, disjoint_finite_synthesis_norm hp0 hpfin e he hdis]

theorem disjointLpSynthesis_norm (a : lp (fun _ : ι => ℂ) p) :
    ‖disjointLpSynthesis e a‖ = ‖a‖ := by
  refine (finsuppLp_dense p hpfin).induction ?_
    (isClosed_eq (by fun_prop) continuous_norm) a
  rintro x ⟨c, rfl⟩
  rw [disjointLpSynthesis_finite hp0 hpfin e he hdis,
    disjoint_finite_synthesis_norm hp0 hpfin e he hdis]

def disjointLpIsometry : lp (fun _ : ι => ℂ) p →ₗᵢ[ℂ] LebesgueLp p where
  __ := (disjointLpSynthesis e).toLinearMap
  norm_map' := disjointLpSynthesis_norm hp0 hpfin e he hdis

theorem disjointLpSynthesis_single (i : ι) (a : ℂ) :
    disjointLpSynthesis e (lp.single p i a) = a • e i := by
  rw [← finsuppLp_single p i a, disjointLpSynthesis_finite hp0 hpfin e he hdis]
  exact Finsupp.linearCombination_single ..

theorem disjointLpSynthesis_hasSum (a : lp (fun _ : ι => ℂ) p) :
    HasSum (fun i => a i • e i) (disjointLpSynthesis e a) := by
  simpa only [disjointLpSynthesis_single hp0 hpfin e he hdis] using
    (disjointLpSynthesis e).hasSum (lp.hasSum_single hpfin a)

end SchauderTranslates.LpConstruction
