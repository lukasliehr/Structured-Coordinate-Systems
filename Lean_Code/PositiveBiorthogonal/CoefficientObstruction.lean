import Lean_Code.PositiveBiorthogonal.PairingNorms
import Lean_Code.PositiveBiorthogonal.SupportObstruction
import Lean_Code.PositiveBiorthogonal.BasisCriterion

/-! Strictness of the first projection for nonnegative represented coefficients. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

/-- Equality in the positive pairing forces positivity of the primal vector.
The product normalization avoids changing either basis sequence. -/
theorem forced_positive [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
    (hpfin : p ≠ ∞) (b : L 𝕜 p) (g : L 𝕜 q) (hg : Nonnegative g)
    (hpair : pairing b g = 1) (hnorm : ‖b‖ * ‖g‖ = 1) : Nonnegative b := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let raw := fun x : ℝ => ((max (RCLike.re (b x)) 0 : ℝ) : 𝕜)
  have hrawnorm (x : ℝ) : ‖raw x‖ = max (RCLike.re (b x)) 0 := by
    simp only [raw, RCLike.norm_ofReal]
    exact abs_of_nonneg (le_max_right (RCLike.re (b x)) 0)
  have hrawle (x : ℝ) : ‖raw x‖ ≤ ‖b x‖ := by
    rw [hrawnorm]
    exact max_le (RCLike.re_le_norm _) (norm_nonneg _)
  have hraw : MemLp raw p volume := by
    apply (Lp.memLp b).of_le _ (Eventually.of_forall hrawle)
    exact (RCLike.continuous_ofReal.comp_stronglyMeasurable
      ((show Continuous (fun y : ℝ => max y 0) from continuous_id.max continuous_const).comp_stronglyMeasurable
          (RCLike.continuous_re.comp_stronglyMeasurable (Lp.stronglyMeasurable b)))).aestronglyMeasurable
  let h : L 𝕜 p := hraw.toLp raw
  have hle : ∀ᵐ x : ℝ, ‖h x‖ ≤ ‖b x‖ := by
    filter_upwards [hraw.coeFn_toLp] with x hx
    change ‖hraw.toLp raw x‖ ≤ _
    rw [hx]
    exact hrawle x
  have hnormle : ‖h‖ ≤ ‖b‖ := Lp.norm_le_norm_of_ae_le hle
  have hprodle : ∀ᵐ x : ℝ, RCLike.re (b x * g x) ≤ RCLike.re (h x * g x) := by
    filter_upwards [hg, hraw.coeFn_toLp] with x hgx hx
    change RCLike.re (b x * g x) ≤ RCLike.re (hraw.toLp raw x * g x)
    rw [hx]
    simp only [RCLike.mul_re, (RCLike.nonneg_iff.mp hgx).2, mul_zero,
      sub_zero, raw, RCLike.ofReal_re]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (RCLike.nonneg_iff.mp hgx).1
  have hib := (Lp.memLp b).integrable_mul (Lp.memLp g)
  have hih := (Lp.memLp h).integrable_mul (Lp.memLp g)
  have hpairle : 1 ≤ RCLike.re (pairing h g) := by
    have hi := integral_mono_ae hib.re hih.re hprodle
    rw [integral_re hib, integral_re hih] at hi
    change RCLike.re (pairing b g) ≤ RCLike.re (pairing h g) at hi
    simpa only [hpair, RCLike.one_re] using hi
  have hnormge : 1 ≤ ‖h‖ * ‖g‖ :=
    hpairle.trans ((RCLike.re_le_norm _).trans (norm_pairing_le h g))
  have hgnorm : 0 < ‖g‖ := by
    have := norm_nonneg b
    have := norm_nonneg g
    nlinarith
  have heq : ‖h‖ = ‖b‖ := by nlinarith
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hae := ae_norm_eq_of_le_of_norm_eq h b hp0 hpfin hle heq
  filter_upwards [hae, hraw.coeFn_toLp] with x hx he
  change ‖hraw.toLp raw x‖ = ‖b x‖ at hx
  rw [he, hrawnorm] at hx
  apply RCLike.nonneg_iff.mpr
  have hre : RCLike.re (b x) = ‖b x‖ := by
    by_cases hpos : 0 ≤ RCLike.re (b x)
    · simpa only [max_eq_left hpos] using hx
    · rw [max_eq_right (le_of_not_ge hpos)] at hx
      have hbzero := norm_eq_zero.mp hx.symm
      simp [hbzero]
  refine ⟨by rw [hre]; exact norm_nonneg _, ?_⟩
  exact RCLike.im_eq_zero_of_le hre.symm.le

theorem coefficient_first_projection_strict [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
    (hpfin : p ≠ ∞) (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q)
    (hγ : Represents B γ) (hpos : ∀ n, Nonnegative (γ n)) : 1 < ‖P B 1‖ := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  by_contra! hle
  have hnormP : ‖P B 1‖ = 1 := le_antisymm hle (one_le_firstProjection B)
  have hcoeff : B.coeff 0 = representedFunctional (p := p) (γ 0) := by
    ext f
    simpa only [representedFunctional_apply] using hγ 0 f
  have hnorm : ‖B.b 0‖ * ‖γ 0‖ = 1 := by
    rw [← represented_rank_one_norm, ← hcoeff]
    simpa only [P, Finset.range_one, Finset.sum_singleton] using hnormP
  have hpair : pairing (B.b 0) (γ 0) = 1 := by
    simpa using represented_pairing_biorthogonal B γ hγ 0 0
  have hbpos := forced_positive hpfin (B.b 0) (γ 0) (hpos 0) hpair hnorm
  let E := {x : ℝ | 0 < RCLike.re (B.b 0 x)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (RCLike.continuous_re.comp_stronglyMeasurable (Lp.stronglyMeasurable (B.b 0))).measurable
  have hEpos : 0 < volume E := by
    by_contra! hz
    have hae : ∀ᵐ x : ℝ, ¬ 0 < RCLike.re (B.b 0 x) := by
      rw [ae_iff]
      simpa only [not_not] using le_antisymm hz bot_le
    apply StatementAudit.basis_vector_ne_zero B 0
    apply Lp.ext
    filter_upwards [hbpos, hae, Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)] with x hx he hzero
    rw [hzero, Pi.zero_apply]
    apply RCLike.ext
    · simpa only [RCLike.zero_re] using le_antisymm (le_of_not_gt he) (RCLike.nonneg_iff.mp hx).1
    · simpa only [RCLike.zero_im] using (RCLike.nonneg_iff.mp hx).2
  have hvanish (n : ℕ) (hn : n ≠ 0) : ∀ᵐ x : ℝ, x ∈ E → γ n x = 0 := by
    apply zero_product_on_positive_rclike hbpos (hpos n)
      ((Lp.memLp (B.b 0)).integrable_mul (Lp.memLp (γ n)))
    change pairing (B.b 0) (γ n) = 0
    simpa only [if_neg (Ne.symm hn)] using represented_pairing_biorthogonal B γ hγ 0 n
  apply supported_space_not_one_dimensional E hE hEpos (B.b 0)
  intro f hf
  have hzero (n : ℕ) (hn : n ≠ 0) : B.coeff n f = 0 := by
    rw [hγ]
    unfold pairing
    apply integral_eq_zero_of_ae
    filter_upwards [hf, hvanish n hn] with x hfx hnx
    by_cases hx : x ∈ E
    · simp only [hnx hx, mul_zero, Pi.zero_apply]
    · simp only [hfx hx, zero_mul, Pi.zero_apply]
  have hsum (N : ℕ) (hN : 1 ≤ N) :
      ∑ n ∈ Finset.range N, B.coeff n f • B.b n = B.coeff 0 f • B.b 0 := by
    apply Finset.sum_eq_single 0
    · intro n _ hn
      rw [hzero n hn, zero_smul]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, B.coeff n f • B.b n)
      atTop (𝓝 (B.coeff 0 f • B.b 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hsum N hN).symm
  exact Submodule.mem_span_singleton.mpr ⟨B.coeff 0 f, tendsto_nhds_unique hlim (B.expansion f)⟩

end PositiveBiorthogonal
