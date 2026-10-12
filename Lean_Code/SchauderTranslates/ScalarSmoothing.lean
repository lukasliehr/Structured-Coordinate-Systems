import Lean_Code.SchauderTranslates.ScalarFejerLimits

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Positive polynomial means of an actual scalar block. Frequencies and order are fixed;
raw floors, raw coefficient prefixes, and inverse diagonals are retained exactly. Centered
Grams and gain converge, and every strict centered-prefix margin is retained eventually. -/
theorem fejer_smoothing_data {d n : ℕ} (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) :
    ∃ t : ℕ → ScalarData d n,
      (∀ N, (t N).frequencies = s.frequencies ∧ (t N).IsPolynomial ∧
        (∀ x, b ≤ (t N).density x) ∧ (t N).mass = s.mass ∧
        (s.IsEven → (t N).IsEven) ∧
        (∀ σ : ℝ, (s.rawGram - (σ : ℂ) • 1).PosSemidef →
          ((t N).rawGram - (σ : ℂ) • 1).PosSemidef) ∧
        (∀ q : ℝ, 0 ≤ q → s.AugmentedPrefixSqBound q → (t N).AugmentedPrefixSqBound q) ∧
        (∀ i, ((t N).rawGram⁻¹ i i).re ≤ (s.rawGram⁻¹ i i).re)) ∧
      Tendsto (fun N => (t N).rawGram) atTop (𝓝 s.rawGram) ∧
      Tendsto (fun N => (t N).rawGram⁻¹) atTop (𝓝 s.rawGram⁻¹) ∧
      Tendsto (fun N => (t N).centeredGram) atTop (𝓝 s.centeredGram) ∧
      Tendsto (fun N => (t N).gain) atTop (𝓝 s.gain) ∧
      (∀ q r : ℝ, 0 ≤ q → q < r → s.CenteredPrefixSqBound q →
        ∀ᶠ N in atTop, (t N).CenteredPrefixSqBound r) := by
  refine ⟨s.fejer hb hf, ?_, s.fejer_rawGram_tendsto hb hf,
    s.fejer_rawGram_inverse_tendsto hb hf, s.fejer_centeredGram_tendsto hb hf,
    s.fejer_gain_tendsto hb hf, fun q r hq hqr hp => s.fejer_centered_prefix_eventually hb hf hq hqr hp⟩
  intro N
  exact ⟨rfl, s.fejer_polynomial hb hf N, s.fejer_floor hb hf N,
    s.fejer_mass hb hf N, fun he => s.fejer_even hb hf he N,
    fun σ hσ => s.fejer_matrix_floor hb hf N hσ,
    fun q hq hp => s.fejer_augmented_prefix hb hf N hq hp,
    s.fejer_inverse_diagonal hb hf N⟩

end SchauderTranslates
