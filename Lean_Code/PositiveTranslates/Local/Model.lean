import Lean_Code.PositiveTranslates.Local.RootVector
import Lean_Code.PositiveTranslates.Local.StepBridge

/-!
# The model basis of `Lᵖ(ℝ)`

For `1 < p < ∞` and every `B > 1` the non-negative Schauder basis of `Lᵖ(ℝ)` constructed in
`Lean_Code/PositiveBiorthogonal`, normalized in `Lᵖ`, is a `LocalBasis p r Set.univ B` whose
first vector is the indicator of the unit interval, `r 0 = intervalAtom p (0, 1)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The partial sum projection of a basis, evaluated on a finite combination of the basis
vectors, is the corresponding prefix. -/
theorem Local.P_linearCombination (Δ : PositiveBiorthogonal.SchauderBasis ℂ p) (N : ℕ)
    (c : ℕ →₀ ℂ) :
    PositiveBiorthogonal.P Δ N (Finsupp.linearCombination ℂ Δ.b c) =
      ∑ n ∈ Finset.range N, c n • Δ.b n := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  | single m x =>
    rw [Finsupp.linearCombination_single, map_smul, StatementAudit.P_apply]
    simp only [Δ.biorthogonal, Finsupp.single_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : m = n <;> simp [h]

/-- A Schauder basis of `Lᵖ(ℝ)` consisting of non-negative compactly supported step
functions, normalized in `Lᵖ`, is a local basis of the whole line. The prefix constant is any
bound for the basis constant. -/
theorem localBasis_of_positiveBasis (Γ : PositiveBiorthogonal.SchauderBasis ℂ p)
    (hpos : PositiveBiorthogonal.PositiveBasis Γ)
    (hstep : ∀ n, PositiveBiorthogonal.CompactlySupportedStep (Γ.b n))
    {B : ℝ} (hK : PositiveBiorthogonal.K Γ ≤ B) :
    LocalBasis p (fun n => ((‖Γ.b n‖⁻¹ : ℝ) : ℂ) • Γ.b n) Set.univ B := by
  have hne : ∀ n, Γ.b n ≠ 0 := StatementAudit.basis_vector_ne_zero Γ
  have hnp : ∀ n, 0 < ‖Γ.b n‖ := fun n => norm_pos_iff.mpr (hne n)
  have ha : ∀ n, ((‖Γ.b n‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    fun n => Complex.ofReal_ne_zero.mpr (inv_ne_zero (hnp n).ne')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [ofReal_smul_eq]
    exact (isCompactStep_of_step_of_nonneg (hstep n) (hpos n)).smul _
  · intro n
    filter_upwards [hpos n, Lp.coeFn_smul ((‖Γ.b n‖⁻¹ : ℝ) : ℂ) (Γ.b n)] with x hx hs
    rw [hs, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr (inv_nonneg.mpr (norm_nonneg _))) hx
  · intro n
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hnp n)),
      inv_mul_cancel₀ (hnp n).ne']
  · intro n
    exact Filter.Eventually.of_forall (fun x hx => absurd (Set.mem_univ x) hx)
  · intro F _
    apply mem_closure_of_tendsto (Γ.expansion F)
    refine Filter.Eventually.of_forall (fun N => ?_)
    apply Submodule.sum_mem
    intro n _
    apply Submodule.smul_mem
    have hb : Γ.b n = ((‖Γ.b n‖ : ℝ) : ℂ) • (((‖Γ.b n‖⁻¹ : ℝ) : ℂ) • Γ.b n) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (hnp n).ne', Complex.ofReal_one,
        one_smul]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · intro N c
    have hP := P_linearCombination (Γ.rescale _ ha) N c
    rw [Γ.rescale_projection] at hP
    change PositiveBiorthogonal.P Γ N
        (Finsupp.linearCombination ℂ (fun n => ((‖Γ.b n‖⁻¹ : ℝ) : ℂ) • Γ.b n) c) =
      ∑ n ∈ Finset.range N, c n • (((‖Γ.b n‖⁻¹ : ℝ) : ℂ) • Γ.b n) at hP
    rw [← hP]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      ((PositiveBiorthogonal.projection_le_K Γ N).trans hK) (norm_nonneg _))

/-- **Model basis.** For `1 < p < ∞` and `B > 1` there is a normalized non-negative
compact-step Schauder basis of `Lᵖ(ℝ)` with prefix constant `B` whose first vector is the
indicator of `[0, 1)`. -/
theorem exists_model_basis (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) :
    ∃ r : ℕ → LebesgueLp p, r 0 = intervalAtom p (0, 1) ∧ LocalBasis p r Set.univ B := by
  obtain ⟨Γ, hroot, hpos, hstep, hK⟩ :=
    PositiveBiorthogonal.exists_almost_monotone_positive_basis_with_root ℂ p hp1
      hpfin.lt_top (B - 1) (sub_pos.mpr hB)
  have hK' : PositiveBiorthogonal.K Γ ≤ B := by linarith
  have hp0 : p ≠ 0 := exponent_ne_zero
  refine ⟨_, ?_, localBasis_of_positiveBasis Γ hpos hstep hK'⟩
  have h0 : Γ.b 0 = intervalAtom p (0, 1) := by
    rw [hroot]
    exact gridUnit_indicator_eq_intervalAtom p
  change ((‖Γ.b 0‖⁻¹ : ℝ) : ℂ) • Γ.b 0 = intervalAtom p (0, 1)
  rw [h0, initial_generator_unit p hp0 hpfin]
  simp

end StructuredBases.PositiveTranslates
