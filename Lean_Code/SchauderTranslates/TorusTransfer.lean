import Lean_Code.SchauderTranslates.Characters
import Lean_Code.SchauderTranslates.FiniteGram

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology FourierTransform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

/-- Pairing an integer Fourier mode with a real transfer direction. -/
def frequencyDot {d : ℕ} (k : Fin d → ℤ) (ω : Fin d → ℝ) : ℝ :=
  ∑ i, (k i : ℝ) * ω i

theorem frequencyDot_sub {d : ℕ} (k l : Fin d → ℤ) (ω : Fin d → ℝ) :
    frequencyDot (k - l) ω = frequencyDot k ω - frequencyDot l ω := by
  simp [frequencyDot, sub_mul, Finset.sum_sub_distrib]

theorem exists_direction_avoiding_modes {d : ℕ} (K : Finset (Fin d → ℤ)) :
    ∃ ω : Fin d → ℝ, ∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0 := by
  classical
  let D := K.erase 0
  let f (k : D) : Module.Dual ℝ (Fin d → ℝ) :=
    ∑ i, ((k.val i : ℤ) : ℝ) • LinearMap.proj i
  have hf : ∀ k : D, ∃ ω, f k ω ≠ 0 := by
    intro k
    have hk : k.val ≠ 0 := (Finset.mem_erase.mp k.property).1
    obtain ⟨j, hj⟩ : ∃ j, k.val j ≠ 0 := by
      by_contra! h
      exact hk (funext h)
    refine ⟨Pi.single j 1, ?_⟩
    simpa [f, LinearMap.sum_apply, LinearMap.smul_apply, Pi.single_apply] using hj
  obtain ⟨ω, hω⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨ω, fun k hk hk0 => ?_⟩
  simpa [f, frequencyDot, LinearMap.sum_apply, LinearMap.smul_apply] using
    hω ⟨k, Finset.mem_erase.mpr ⟨hk0, hk⟩⟩

/-- A direction separates all required modes and all frequencies at every sufficiently large scale. -/
theorem avoid_frequency_collisions {d : ℕ}
    (pairs : Finset (ℝ × (Fin d → ℤ))) (K : Finset (Fin d → ℤ)) :
    ∃ ω : Fin d → ℝ,
      (∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0) ∧
      ∀ᶠ A : ℝ in atTop,
        Set.InjOn (fun p : ℝ × (Fin d → ℤ) => p.1 + A * frequencyDot p.2 ω) pairs := by
  classical
  let D := K ∪ (pairs.product pairs).image (fun pq => pq.1.2 - pq.2.2)
  obtain ⟨ω, hω⟩ := exists_direction_avoiding_modes D
  refine ⟨ω, fun k hk => hω k (Finset.mem_union_left _ hk), ?_⟩
  have hpair (p q : ℝ × (Fin d → ℤ)) (hp : p ∈ pairs) (hq : q ∈ pairs) :
      ∀ᶠ A : ℝ in atTop,
        p.1 + A * frequencyDot p.2 ω = q.1 + A * frequencyDot q.2 ω → p = q := by
    by_cases hk : p.2 = q.2
    · exact Eventually.of_forall (fun A he => Prod.ext (by simpa [hk] using he) hk)
    have hd : frequencyDot p.2 ω - frequencyDot q.2 ω ≠ 0 := by
      rw [← frequencyDot_sub]
      apply hω _ _ (sub_ne_zero.mpr hk)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩)
    filter_upwards [eventually_gt_atTop ((q.1 - p.1) /
      (frequencyDot p.2 ω - frequencyDot q.2 ω))] with A hA
    intro he
    have hroot : A = (q.1 - p.1) / (frequencyDot p.2 ω - frequencyDot q.2 ω) :=
      (eq_div_iff hd).mpr (by nlinarith [he])
    exact False.elim ((ne_of_gt hA) hroot)
  have hall : ∀ᶠ A : ℝ in atTop, ∀ p ∈ pairs, ∀ q ∈ pairs,
      p.1 + A * frequencyDot p.2 ω = q.1 + A * frequencyDot q.2 ω → p = q := by
    simp only [Filter.eventually_all_finset]
    exact fun p hp q hq => hpair p q hp hq
  exact hall

theorem integral_mul_character_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    (∫ t, f t * character ξ t) = 𝓕 f (-ξ) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  have he : (↑(-2 * Real.pi * inner ℝ t (-ξ)) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I * ξ * t := by
    simp only [Real.inner_apply]
    push_cast
    ring
  change f t * character ξ t =
    Complex.exp ((↑(-2 * Real.pi * inner ℝ t (-ξ)) : ℂ) * Complex.I) * f t
  rw [he]
  exact mul_comm _ _

/-- Every nonconstant transferred Fourier mode vanishes at large scales. -/
theorem oscillatory_integral_tendsto_zero (f : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, f t * character (A * c) t) atTop (𝓝 0) := by
  have hfreq : Tendsto (fun A : ℝ => -(A * c)) atTop (cocompact ℝ) := by
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have h := tendsto_id.atTop_mul_const (neg_pos.mpr hneg)
      simpa only [mul_neg, id_eq] using h.mono_right atTop_le_cocompact
    · have h := tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hpos)
      simpa only [Function.comp_def, id_eq] using h.mono_right atBot_le_cocompact
  simpa only [integral_mul_character_eq_fourier, Function.comp_def] using
    (Real.zero_at_infty_fourier f).comp hfreq

/-- Finite Fourier sums average to their zero mode. Coefficients may be any L¹ functions. -/
theorem finite_moment_transfer_zero_mode {d : ℕ} (K : Finset (Fin d → ℤ))
    (f : (Fin d → ℤ) → ℝ → ℂ) (hf : ∀ k ∈ K, Integrable (f k))
    (ω : Fin d → ℝ) (hω : ∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, ∑ k ∈ K, f k t * character (A * frequencyDot k ω) t)
      atTop (𝓝 (∑ k ∈ K, if k = 0 then ∫ t, f k t else 0)) := by
  classical
  have hi (A : ℝ) (k : Fin d → ℤ) (hk : k ∈ K) :
      Integrable (fun t => f k t * character (A * frequencyDot k ω) t) := by
    apply (hf k hk).mul_bdd (c := 1) (continuous_character _).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by simp)
  simp_rw [integral_finsetSum K (hi _)]
  apply tendsto_finsetSum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [frequencyDot, character]
  · simpa only [if_neg hk0] using oscillatory_integral_tendsto_zero (f k) (hω k hk hk0)

/-- Normalized Haar probability measure on the finite torus. -/
def torusMeasure (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

theorem torusMeasure_eq_volume (d : ℕ) : torusMeasure d = volume := by
  change Measure.pi (fun _ => AddCircle.haarAddCircle) =
    Measure.pi (fun _ => (volume : Measure UnitAddCircle))
  simp [AddCircle.volume_eq_smul_haarAddCircle]

instance torusMeasure_probability (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

theorem integral_torus_character {d : ℕ} (k : Fin d → ℤ) :
    (∫ y, UnitAddTorus.mFourier k y ∂torusMeasure d) = if k = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) 0 k
  simpa only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add, neg_zero, zero_add, add_zero, eq_comm] using! h

theorem torus_character_on_line {d : ℕ} (k : Fin d → ℤ) (ω : Fin d → ℝ) (A t : ℝ) :
    UnitAddTorus.mFourier k (fun i => ((A * ω i * t : ℝ) : UnitAddCircle)) =
      character (A * frequencyDot k ω) t := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum]
  unfold character frequencyDot
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A finite Fourier expansion, with coefficients depending on the line variable. -/
def torusPolynomial {d : ℕ} (K : Finset (Fin d → ℤ))
    (p : (Fin d → ℤ) → ℝ → ℂ) (t : ℝ) (y : UnitAddTorus (Fin d)) : ℂ :=
  ∑ k ∈ K, p k t * UnitAddTorus.mFourier k y

theorem integral_torusPolynomial {d : ℕ} (K : Finset (Fin d → ℤ))
    (p : (Fin d → ℤ) → ℝ → ℂ) (t : ℝ) :
    (∫ y, torusPolynomial K p t y ∂torusMeasure d) =
      ∑ k ∈ K, if k = 0 then p k t else 0 := by
  classical
  have hi (k : Fin d → ℤ) : Integrable
      (fun y => p k t * UnitAddTorus.mFourier k y) (torusMeasure d) := by
    apply Integrable.const_mul
    exact (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold torusPolynomial
  rw [integral_finsetSum K (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_torus_character]
  split_ifs <;> simp

/-- The actual torus-to-line averaging identity, allowing integrable coefficient functions. -/
theorem finite_moment_transfer {d : ℕ} (K : Finset (Fin d → ℤ))
    (f : (Fin d → ℤ) → ℝ → ℂ) (hf : ∀ k ∈ K, Integrable (f k))
    (ω : Fin d → ℝ) (hω : ∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, torusPolynomial K f t
      (fun i => ((A * ω i * t : ℝ) : UnitAddCircle))) atTop
      (𝓝 (∫ t, ∫ y, torusPolynomial K f t y ∂torusMeasure d)) := by
  classical
  have hi : ∀ k ∈ K, Integrable (fun t => if k = 0 then f k t else 0) := by
    intro k hk
    split_ifs
    · exact hf k hk
    · exact integrable_zero _ _ _
  simp_rw [integral_torusPolynomial, integral_finsetSum K hi]
  have he : (∑ k ∈ K, ∫ t, if k = 0 then f k t else 0) =
      ∑ k ∈ K, if k = 0 then ∫ t, f k t else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  rw [he]
  simpa only [torusPolynomial, torus_character_on_line] using
    finite_moment_transfer_zero_mode K f hf ω hω

/-- The paper's bounded-coefficient formulation: the common weight is absorbed into L¹. -/
theorem finite_moment_transfer_weighted {d : ℕ} (K : Finset (Fin d → ℤ))
    (p : (Fin d → ℤ) → ℝ → ℂ) (h : ℝ → ℂ) (hh : Integrable h)
    (hp : ∀ k ∈ K, AEStronglyMeasurable (p k) volume)
    (hb : ∀ k ∈ K, ∃ C : ℝ, ∀ᵐ t, ‖p k t‖ ≤ C)
    (ω : Fin d → ℝ) (hω : ∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, h t * torusPolynomial K p t
      (fun i => ((A * ω i * t : ℝ) : UnitAddCircle))) atTop
      (𝓝 (∫ t, h t * ∫ y, torusPolynomial K p t y ∂torusMeasure d)) := by
  have hi : ∀ k ∈ K, Integrable (fun t => h t * p k t) := by
    intro k hk
    obtain ⟨C, hC⟩ := hb k hk
    exact hh.mul_bdd (hp k hk) hC
  have he (t : ℝ) (y : UnitAddTorus (Fin d)) :
      torusPolynomial K (fun k t => h t * p k t) t y = h t * torusPolynomial K p t y := by
    simp only [torusPolynomial, Finset.mul_sum, mul_assoc]
  simpa only [he, integral_const_mul] using
    finite_moment_transfer K (fun k t => h t * p k t) hi ω hω

/-- A finite collection has one common threshold for any prescribed open neighborhood. -/
theorem finite_moments_simultaneous {ι : Type*} [Finite ι]
    (M : ι → ℝ → ℂ) (L : ι → ℂ) (h : ∀ i, Tendsto (M i) atTop (𝓝 (L i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A ≥ A₀, ∀ i, ‖M i A - L i‖ < ε := by
  have hi (i : ι) : ∀ᶠ A in atTop, ‖M i A - L i‖ < ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp (h i) ε hε)
  exact eventually_atTop.mp (Filter.eventually_all.mpr hi)

end SchauderTranslates
