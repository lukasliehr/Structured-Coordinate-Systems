import Lean_Code.SchauderTranslates.FejerCorrelation
import Lean_Code.SchauderTranslates.SchurSmoothing
import Lean_Code.SchauderTranslates.AugmentedScalarPrefixes
import Lean_Code.SchauderTranslates.FiniteGram

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Polynomial smoothing retains the exact character list and its order. -/
def fejer (s : ScalarData d n) {b : ℝ} (hb : 0 < b) (hf : ∀ x, b ≤ s.density x)
    (N : ℕ) : ScalarData d n where
  toTorusWeight := s.toTorusWeight.fejer hb hf N
  frequencies := s.frequencies
  injective := s.injective
  nonconstant := s.nonconstant

@[simp] theorem fejer_mass (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) : (s.fejer hb hf N).mass = s.mass :=
  s.toTorusWeight.fejer_mass hb hf N

theorem fejer_floor (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) : ∀ x, b ≤ (s.fejer hb hf N).density x :=
  s.toTorusWeight.fejer_floor hb hf N

theorem fejer_even (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (hs : s.IsEven) (N : ℕ) : (s.fejer hb hf N).IsEven :=
  s.toTorusWeight.fejerDensity_even hs N

theorem fejer_polynomial (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) : (s.fejer hb hf N).IsPolynomial :=
  s.toTorusWeight.fejerDensity_polynomial N

theorem rawGram_moment (s : ScalarData d n) (i j : Unit ⊕ Fin n) :
    s.rawGram i j = torusFourierMoment (fun x => (s.density x : ℂ))
      (s.augmentedFrequency i - s.augmentedFrequency j) :=
  s.toTorusWeight.vector_inner_moment _ _

/-- The actual smoothed raw Gram is the Schur product with a correlation matrix. -/
theorem fejer_rawGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) :
    (s.fejer hb hf N).rawGram = s.rawGram ⊙ fejerCorrelation s.augmentedFrequency N := by
  ext i j
  rw [rawGram_moment, Matrix.hadamard_apply, rawGram_moment]
  exact s.toTorusWeight.fejerDensity_moment N _

theorem fejer_rawGram_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) :
    Tendsto (fun N => (s.fejer hb hf N).rawGram) atTop (𝓝 s.rawGram) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [rawGram_moment, fejer, TorusWeight.fejer, augmentedFrequency] using
    s.toTorusWeight.fejerDensity_moment_tendsto (s.augmentedFrequency i - s.augmentedFrequency j)

theorem fejer_matrix_floor (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) {σ : ℝ}
    (hσ : (s.rawGram - (σ : ℂ) • 1).PosSemidef) :
    ((s.fejer hb hf N).rawGram - (σ : ℂ) • 1).PosSemidef := by
  rw [s.fejer_rawGram hb hf N]
  exact schur_preserves_floor (fejerCorrelation_posSemidef _ N) (fejerCorrelation_diag _ N) hσ

theorem fejer_inverse_diagonal (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) (i : Unit ⊕ Fin n) :
    ((s.fejer hb hf N).rawGram⁻¹ i i).re ≤ (s.rawGram⁻¹ i i).re := by
  have hpd := (s.fejer hb hf N).rawGram_posDef
  rw [s.fejer_rawGram hb hf N] at hpd ⊢
  exact schur_inverse_diagonal_le s.rawGram_posDef (fejerCorrelation_posSemidef _ N)
    (fejerCorrelation_diag _ N) hpd i

theorem fejer_augmented_prefix (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (N : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hp : s.AugmentedPrefixSqBound q) : (s.fejer hb hf N).AugmentedPrefixSqBound q := by
  apply ((s.fejer hb hf N).augmentedPrefixSqBound_iff_gram hq).mpr
  intro k
  have hpd := (s.fejer hb hf N).rawGram_posDef
  rw [s.fejer_rawGram hb hf N] at hpd ⊢
  exact schur_preserves_prefix s.rawGram_posDef (fejerCorrelation_posSemidef _ N) hpd
    _ hq ((s.augmentedPrefixSqBound_iff_gram hq).mp hp k)

/-- Inverse convergence uses the positive definite limit, with no uniform bound assumption. -/
theorem fejer_rawGram_inverse_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) :
    Tendsto (fun N => (s.fejer hb hf N).rawGram⁻¹) atTop (𝓝 s.rawGram⁻¹) :=
  (gram_inverse_continuousAt s.rawGram_posDef).tendsto.comp (s.fejer_rawGram_tendsto hb hf)

end ScalarData
end SchauderTranslates
