import Lean_Code.SchauderTranslates.Contracts
import Lean_Code.SchauderTranslates.Characters
import Lean_Code.SchauderTranslates.WeightedIsometry

/-!
# Limit stages: elementary estimates for raw weighted norms

Basic facts about `normSq`, `distanceSq` and finite character sums used by the
infinite stage construction (blueprint nodes `limit:stages`, `limit:errors`,
`limit:prefix`):

* the Gaussian reference probability density;
* nonnegativity, infimum characterisations and monotonicity of `distanceSq`
  under decreasing weights and extended lists;
* the bridge `‖f‖² = normSq w F` between weighted `L²` classes and their
  bounded representatives;
* convergence of raw weighted norms of bounded continuous functions under
  `L¹` convergence of densities.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SchauderTranslates.LimitAssembly
open SchauderTranslates.Construction

/-! ### The Gaussian reference weight -/

/-- The Gaussian reference density `t ↦ exp (-π t²)`. -/
def gaussWeight : Weight where
  density t := Real.exp (-Real.pi * t ^ 2)
  measurable := by fun_prop
  integrable := integrable_exp_neg_mul_sq Real.pi_pos
  positive := Eventually.of_forall (fun _ => Real.exp_pos _)

theorem gaussWeight_density (t : ℝ) : gaussWeight.density t = Real.exp (-Real.pi * t ^ 2) :=
  rfl

theorem gaussWeight_density_pos (t : ℝ) : 0 < gaussWeight.density t :=
  Real.exp_pos _

theorem gaussWeight_integral : (∫ t, gaussWeight.density t) = 1 := by
  change (∫ t, Real.exp (-Real.pi * t ^ 2)) = 1
  rw [integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]

/-! ### Raw norms and distances -/

theorem normSq_nonneg (w : Weight) (f : ℝ → ℂ) : 0 ≤ normSq w f := by
  unfold normSq
  apply integral_nonneg_of_ae
  filter_upwards [w.positive] with t ht
  exact mul_nonneg (pow_nonneg (norm_nonneg _) 2) ht.le

theorem normSq_zero (w : Weight) : normSq w (fun _ => 0) = 0 := by
  simp [normSq]

theorem distanceSq_bddBelow (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ) :
    BddBelow (Set.range (fun c : Fin d → ℂ =>
      normSq w (fun t => character ξ t - synthesis μ c t))) :=
  ⟨0, by rintro _ ⟨c, rfl⟩; exact normSq_nonneg _ _⟩

theorem distanceSq_nonneg (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ) :
    0 ≤ distanceSq w μ ξ :=
  le_csInf (Set.range_nonempty _) (by rintro _ ⟨c, rfl⟩; exact normSq_nonneg _ _)

theorem distanceSq_le_normSq (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ)
    (c : Fin d → ℂ) :
    distanceSq w μ ξ ≤ normSq w (fun t => character ξ t - synthesis μ c t) :=
  csInf_le (distanceSq_bddBelow w μ ξ) ⟨c, rfl⟩

theorem exists_normSq_lt_of_distanceSq_lt (w : Weight) {d : ℕ} (μ : Fin d → ℝ)
    {ξ ε : ℝ} (h : distanceSq w μ ξ < ε) :
    ∃ c : Fin d → ℂ, normSq w (fun t => character ξ t - synthesis μ c t) < ε := by
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) h
  exact ⟨c, hc⟩

/-! ### Finite character sums -/

theorem continuous_synthesis {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) :
    Continuous (synthesis μ c) := by
  unfold synthesis
  fun_prop

theorem norm_synthesis_le {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖synthesis μ c t‖ ≤ ∑ i, ‖c i‖ := by
  unfold synthesis
  calc
    ‖∑ i, c i * character (μ i) t‖ ≤ ∑ i, ‖c i * character (μ i) t‖ := norm_sum_le _ _
    _ = ∑ i, ‖c i‖ := by simp [norm_character]

theorem continuous_residual {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) (ξ : ℝ) :
    Continuous (fun t => character ξ t - synthesis μ c t) :=
  (continuous_character ξ).sub (continuous_synthesis μ c)

theorem norm_residual_le {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) (ξ t : ℝ) :
    ‖character ξ t - synthesis μ c t‖ ≤ 1 + ∑ i, ‖c i‖ := by
  calc
    ‖character ξ t - synthesis μ c t‖ ≤ ‖character ξ t‖ + ‖synthesis μ c t‖ := norm_sub_le _ _
    _ ≤ 1 + ∑ i, ‖c i‖ := by rw [norm_character]; linarith [norm_synthesis_le μ c t]

theorem continuous_finsetSum_character {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (fun t => ∑ i ∈ s, a i * character (ξ i) t) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_character (ξ i)))

theorem norm_finsetSum_character_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ)
    (t : ℝ) : ‖∑ i ∈ s, a i * character (ξ i) t‖ ≤ ∑ i ∈ s, ‖a i‖ := by
  calc
    ‖∑ i ∈ s, a i * character (ξ i) t‖ ≤ ∑ i ∈ s, ‖a i * character (ξ i) t‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ s, ‖a i‖ := by simp [norm_character]

/-- Synthesis over a list stored as a sequence, as a sum over `Finset.range`. -/
theorem synthesis_seq (seq : ℕ → ℝ) (C : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    synthesis (fun i : Fin n => seq i) (fun i => C i) t =
      ∑ i ∈ Finset.range n, C i * character (seq i) t :=
  Fin.sum_univ_eq_sum_range (fun i => C i * character (seq i) t) n

/-- Extension of a finite coefficient vector by zero. -/
def extendCoeff {d : ℕ} (c : Fin d → ℂ) (i : ℕ) : ℂ :=
  if h : i < d then c ⟨i, h⟩ else 0

theorem extendCoeff_fin {d : ℕ} (c : Fin d → ℂ) : (fun i : Fin d => extendCoeff c i) = c := by
  funext i
  simp [extendCoeff, i.isLt]

theorem extendCoeff_of_le {d : ℕ} (c : Fin d → ℂ) {i : ℕ} (hi : d ≤ i) :
    extendCoeff c i = 0 := by
  simp [extendCoeff, not_lt.mpr hi]

/-- A sum over a longer range whose extra terms vanish. -/
theorem sum_range_extend {M : Type*} [AddCommMonoid M] {d e : ℕ} (hde : d ≤ e)
    (f g : ℕ → M) (hfg : ∀ i < d, f i = g i) (hz : ∀ i, d ≤ i → i < e → f i = 0) :
    ∑ i ∈ Finset.range e, f i = ∑ i ∈ Finset.range d, g i := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hde)
    (fun i hi hni => hz i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
      (Finset.mem_range.mp hi))]
  exact Finset.sum_congr rfl (fun i hi => hfg i (Finset.mem_range.mp hi))

/-! ### Integrability and comparison of raw norms -/

theorem integrable_sq_mul {ρ : ℝ → ℝ} (hρ : Integrable ρ) {f : ℝ → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) : Integrable (fun t => ‖f t‖ ^ 2 * ρ t) := by
  refine hρ.bdd_mul (c := B ^ 2) (hf.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hB t) 2

theorem normSq_le_of_density_le {v w : Weight}
    (h : ∀ᵐ t ∂volume, v.density t ≤ w.density t) {f : ℝ → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) : normSq v f ≤ normSq w f := by
  unfold normSq
  apply integral_mono_ae (integrable_sq_mul v.integrable hf hB)
    (integrable_sq_mul w.integrable hf hB)
  filter_upwards [h] with t ht
  exact mul_le_mul_of_nonneg_left ht (pow_nonneg (norm_nonneg _) 2)

/-- Decreasing the weight and extending the list can only decrease the distance. -/
theorem distanceSq_anti_seq {v w : Weight} {d e : ℕ} {seqS seqT : ℕ → ℝ} (hde : d ≤ e)
    (hext : ∀ i < d, seqT i = seqS i) (hw : ∀ᵐ t ∂volume, v.density t ≤ w.density t)
    (ξ : ℝ) :
    distanceSq v (fun i : Fin e => seqT i) ξ ≤ distanceSq w (fun i : Fin d => seqS i) ξ := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  have hs : synthesis (fun i : Fin e => seqT i) (fun i => extendCoeff c i) =
      synthesis (fun i : Fin d => seqS i) c := by
    funext t
    conv_rhs => rw [← extendCoeff_fin c]
    rw [synthesis_seq, synthesis_seq]
    apply sum_range_extend hde
    · intro i hi
      rw [hext i hi]
    · intro i hi _
      rw [extendCoeff_of_le c hi, zero_mul]
  calc
    distanceSq v (fun i : Fin e => seqT i) ξ ≤
        normSq v (fun t => character ξ t -
          synthesis (fun i : Fin e => seqT i) (fun i => extendCoeff c i) t) :=
      distanceSq_le_normSq _ _ _ _
    _ = normSq v (fun t => character ξ t - synthesis (fun i : Fin d => seqS i) c t) := by
      rw [hs]
    _ ≤ normSq w (fun t => character ξ t - synthesis (fun i : Fin d => seqS i) c t) :=
      normSq_le_of_density_le hw (continuous_residual _ c ξ) (norm_residual_le _ c ξ)

/-! ### The bridge to weighted `L²` norms -/

/-- The squared norm of a weighted `L²` class is the raw weighted norm of any representative. -/
theorem norm_sq_eq_normSq (w : Weight) (f : WeightedL2 w) {F : ℝ → ℂ}
    (hf : (f : ℝ → ℂ) =ᵐ[w.measure] F) : ‖f‖ ^ 2 = normSq w F := by
  rw [l2_norm_sq_eq_integral]
  calc
    (∫ t, ‖f t‖ ^ 2 ∂w.measure) = ∫ t, ‖F t‖ ^ 2 ∂w.measure :=
      integral_congr_ae (hf.mono fun t ht => by simp only [ht])
    _ = ∫ t, (ENNReal.ofReal (w.density t)).toReal • ‖F t‖ ^ 2 :=
      integral_withDensity_eq_integral_toReal_smul w.measurable.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    _ = normSq w F := by
      unfold normSq
      apply integral_congr_ae
      filter_upwards [w.positive] with t ht
      rw [ENNReal.toReal_ofReal ht.le, smul_eq_mul, mul_comm]

/-! ### Passing raw norms to an `L¹` limit of densities -/

theorem tendsto_integral_sq_mul {ρ : ℕ → ℝ → ℝ} {ρ' : ℝ → ℝ} (hρ : ∀ m, Integrable (ρ m))
    (hρ' : Integrable ρ')
    (hL1 : Tendsto (fun m => ∫ t, ‖ρ m t - ρ' t‖) atTop (𝓝 0))
    {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) :
    Tendsto (fun m => ∫ t, ‖f t‖ ^ 2 * ρ m t) atTop (𝓝 (∫ t, ‖f t‖ ^ 2 * ρ' t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun m => norm_nonneg _) (g := fun m => B ^ 2 * ∫ t, ‖ρ m t - ρ' t‖)
  · intro m
    rw [← integral_sub (integrable_sq_mul (hρ m) hf hB) (integrable_sq_mul hρ' hf hB)]
    calc
      ‖∫ t, (‖f t‖ ^ 2 * ρ m t - ‖f t‖ ^ 2 * ρ' t)‖ ≤ ∫ t, B ^ 2 * ‖ρ m t - ρ' t‖ := by
        apply norm_integral_le_of_norm_le (((hρ m).sub hρ').norm.const_mul _)
        filter_upwards with t
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB t) 2)
          (norm_nonneg _)
      _ = B ^ 2 * ∫ t, ‖ρ m t - ρ' t‖ := integral_const_mul _ _
  · simpa using hL1.const_mul (B ^ 2)

/-! ### The one-atom prefix bound -/

theorem prefixBound_one (w : Weight) (μ : Fin 1 → ℝ) : PrefixBound w μ 1 := by
  intro k c
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : (fun t => ∑ i : Fin 1, if i.val < 0 then c i * character (μ i) t else 0) =
        fun _ => 0 := by
      funext t
      simp
    rw [h0, normSq_zero, one_pow, one_mul]
    exact normSq_nonneg _ _
  · have h1 : (fun t => ∑ i : Fin 1, if i.val < k then c i * character (μ i) t else 0) =
        synthesis μ c := by
      funext t
      simp [synthesis, hk]
    rw [h1, one_pow, one_mul]

end SchauderTranslates.LimitAssembly
