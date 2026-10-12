import Lean_Code.PositiveBiorthogonal.PositiveDerivative
import Lean_Code.PositiveBiorthogonal.SupportObstruction
import Lean_Code.PositiveBiorthogonal.BasisCriterion

/-! The positive-vector obstruction uses only the given continuous coefficients. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem positive_basis_disjoint_first_support (hp1 : 1 < p) (hpfin : p ≠ ∞)
    (B : SchauderBasis 𝕜 p) (hB : PositiveBasis B) (hcontract : ‖P B 1‖ ≤ 1)
    (n : ℕ) (hn : n ≠ 0) :
    ∀ᵐ x : ℝ, 0 < RCLike.re (B.b 0 x) → B.b n x = 0 := by
  obtain ⟨q, hpq⟩ := StatementAudit.conjugate_exists hp1.le
  let := StatementAudit.conjugate_instance hpq
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hr : 1 < p.toReal := (ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin).lt
  have hnorm (t : ℝ) : ‖B.b 0‖ ≤ ‖B.b 0 - (t : 𝕜) • B.b n‖ := by
    have hfix : P B 1 (B.b 0 - (t : 𝕜) • B.b n) = B.b 0 := by
      simp [StatementAudit.P_one, map_sub, B.biorthogonal, hn]
    calc
      ‖B.b 0‖ = ‖P B 1 (B.b 0 - (t : 𝕜) • B.b n)‖ := congrArg norm hfix.symm
      _ ≤ ‖P B 1‖ * ‖B.b 0 - (t : 𝕜) • B.b n‖ := (P B 1).le_opNorm _
      _ ≤ ‖B.b 0 - (t : 𝕜) • B.b n‖ := by
        simpa using mul_le_mul_of_nonneg_right hcontract (norm_nonneg _)
  have hmin : IsLocalMin (fun t : ℝ => ‖B.b 0 - (t : 𝕜) • B.b n‖ ^ p.toReal) 0 := by
    apply Eventually.of_forall
    intro t
    simpa only [RCLike.ofReal_zero, zero_smul, sub_zero] using
      Real.rpow_le_rpow (norm_nonneg (B.b 0)) (hnorm t) ENNReal.toReal_nonneg
  have hderiv := positive_Lp_norm_power_derivative (q := q) hp1 hpfin (B.b 0) (B.b n) (hB 0) (hB n)
  have hint : (∫ x : ℝ, RCLike.re (B.b 0 x) ^ (p.toReal - 1) * RCLike.re (B.b n x)) = 0 := by
    have heq := hmin.hasDerivAt_eq_zero hderiv
    exact (mul_eq_zero.mp heq).resolve_left (by linarith)
  have hb0pos := (hB 0).mono fun _ hx => (RCLike.nonneg_iff.mp hx).1
  have hbnpos := (hB n).mono fun _ hx => (RCLike.nonneg_iff.mp hx).1
  have hu : ∀ᵐ x : ℝ, 0 ≤ RCLike.re (B.b 0 x) ^ (p.toReal - 1) :=
    hb0pos.mono fun _ hx => Real.rpow_nonneg hx _
  have hi := positive_power_product_integrable (q := q) hp1 hpfin
    (memLp_real_part (B.b 0)) (memLp_real_part (B.b n)) hb0pos
  have hz := zero_product_on_positive hu hbnpos hi hint
  filter_upwards [hz, hB n] with x hx hnx hpos
  apply RCLike.ext
  · simpa only [RCLike.zero_re] using hx (Real.rpow_pos_of_pos hpos _)
  · simpa only [RCLike.zero_im] using (RCLike.nonneg_iff.mp hnx).2

theorem positive_first_projection_strict (hp1 : 1 < p) (hpfin : p ≠ ∞)
    (B : SchauderBasis 𝕜 p) (hB : PositiveBasis B) : 1 < ‖P B 1‖ := by
  by_contra! hcontract
  let E := {x : ℝ | 0 < RCLike.re (B.b 0 x)}
  have hE : MeasurableSet E := positive_support_measurable (B.b 0)
  have hEpos : 0 < volume E :=
    positive_support_measure_pos (B.b 0) (hB 0) (StatementAudit.basis_vector_ne_zero B 0)
  let R : L 𝕜 p →L[𝕜] L 𝕜 p := restriction E hE
  have hR0 : R (B.b 0) = B.b 0 :=
    cut_eq_self E hE (B.b 0) (positive_supported_on_positive_support (B.b 0) (hB 0))
  have hRn (n : ℕ) (hn : n ≠ 0) : R (B.b n) = 0 :=
    cut_eq_zero E hE (B.b n) (positive_basis_disjoint_first_support hp1 hpfin B hB hcontract n hn)
  apply supported_space_not_one_dimensional E hE hEpos (B.b 0)
  intro f hf
  have hRf : R f = f := cut_eq_self E hE f hf
  have hexp := (R.continuous.tendsto f).comp (B.expansion f)
  have hsum (N : ℕ) (hN : 1 ≤ N) :
      R (∑ n ∈ Finset.range N, B.coeff n f • B.b n) = B.coeff 0 f • B.b 0 := by
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_eq_single 0, hR0]
    · intro n _ hn
      rw [hRn n hn, smul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  have hlim : Tendsto (fun N => R (∑ n ∈ Finset.range N, B.coeff n f • B.b n))
      atTop (𝓝 (B.coeff 0 f • B.b 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hsum N hN).symm
  apply Submodule.mem_span_singleton.mpr
  refine ⟨B.coeff 0 f, ?_⟩
  exact (tendsto_nhds_unique hlim hexp).trans hRf

end PositiveBiorthogonal
