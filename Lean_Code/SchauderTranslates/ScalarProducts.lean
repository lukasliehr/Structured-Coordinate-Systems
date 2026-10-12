import Lean_Code.SchauderTranslates.ScalarProductMoments
import Lean_Code.SchauderTranslates.RepeatedMatrix

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Matrix form of the independent-copy centering identity. -/
theorem product_centeredGram (s : ScalarData d n) (L : ℕ) :
    (s.product L).centeredGram = repeatedMatrix L s.centeredGram := by
  ext q r
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective r
  rw [product_centeredGram_entry, repeatedMatrix_entry]

theorem product_mean_vector (s : ScalarData d n) (L : ℕ) :
    (s.product L).mean = repeatedVector L s.mean := by
  funext q
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [product_mean, repeatedVector_entry]

/-- Independent normalized gains add exactly. -/
theorem product_gain (s : ScalarData d n) (L : ℕ) :
    (s.product L).gain = L * s.gain := by
  unfold gain
  rw [product_mean_vector, product_centeredGram,
    repeatedMatrix_inverse _ _ s.centeredGram_posDef.isUnit, repeatedMatrix_quadratic]
  simp

/-- The inverse normalization written in the direction needed for raw estimates. -/
theorem rawCenteredGram_inverse_normalized (s : ScalarData d n) :
    s.rawCenteredGram⁻¹ = (s.mass : ℂ)⁻¹ • s.centeredGram⁻¹ := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  rw [s.centeredGram_inverse, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- Exact raw augmented inverse entry in a copied nonconstant coordinate. -/
theorem product_inverse_nonconstant (s : ScalarData d n) (L : ℕ)
    (i : Fin L) (a : Fin n) :
    (s.product L).rawGram⁻¹ (Sum.inr (finProdFinEquiv (i, a)))
      (Sum.inr (finProdFinEquiv (i, a))) =
        ((s.mass / s.mass ^ L : ℝ) : ℂ) * s.rawCenteredGram⁻¹ a a := by
  have he := congrArg (fun B : Matrix (Fin (L * n)) (Fin (L * n)) ℂ =>
    B (finProdFinEquiv (i, a)) (finProdFinEquiv (i, a)))
      (s.product L).rawGram_inverse_nonconstant
  change (s.product L).rawGram⁻¹ (Sum.inr (finProdFinEquiv (i, a)))
    (Sum.inr (finProdFinEquiv (i, a))) =
      (s.product L).rawCenteredGram⁻¹ (finProdFinEquiv (i, a)) (finProdFinEquiv (i, a)) at he
  rw [he, rawCenteredGram_inverse_normalized, product_centeredGram,
    repeatedMatrix_inverse _ _ s.centeredGram_posDef.isUnit]
  simp only [Matrix.smul_apply, smul_eq_mul, repeatedMatrix_entry, ite_true,
    product_mass, s.centeredGram_inverse, Complex.ofReal_div]
  ring

/-- Conversion to the paper's raw inverse diagonal bound, with the full mass factor. -/
theorem product_inverse_nonconstant_le (s : ScalarData d n) (L : ℕ)
    (i : Fin L) (a : Fin n) {D : ℝ} (hD : (s.rawCenteredGram⁻¹ a a).re ≤ D) :
    ((s.product L).rawGram⁻¹ (Sum.inr (finProdFinEquiv (i, a)))
      (Sum.inr (finProdFinEquiv (i, a)))).re ≤ s.mass * D / s.mass ^ L := by
  rw [product_inverse_nonconstant]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hnonneg : 0 ≤ s.mass / s.mass ^ L :=
    (div_pos s.toTorusWeight.mass_pos (pow_pos s.toTorusWeight.mass_pos _)).le
  calc
    _ ≤ (s.mass / s.mass ^ L) * D := mul_le_mul_of_nonneg_left hD hnonneg
    _ = _ := by ring

end ScalarData

/-- The independent scalar product is an actual scalar torus block. Its normalized centered
Gram is a direct sum, its gain is additive, and raw inverse diagonals have the stated mass
normalization. The formulas also cover the empty product. -/
theorem scalar_product_data {d n : ℕ} (s : ScalarData d n) (L : ℕ) :
    (s.product L).mass = s.mass ^ L ∧
    (s.product L).mean = repeatedVector L s.mean ∧
    (s.product L).centeredGram = repeatedMatrix L s.centeredGram ∧
    (s.product L).gain = L * s.gain ∧
    (∀ (i : Fin L) (a : Fin n) (D : ℝ), (s.rawCenteredGram⁻¹ a a).re ≤ D →
      ((s.product L).rawGram⁻¹ (Sum.inr (finProdFinEquiv (i, a)))
        (Sum.inr (finProdFinEquiv (i, a)))).re ≤ s.mass * D / s.mass ^ L) ∧
    (s.IsEven → (s.product L).IsEven) ∧
    (s.HasPositiveFloor → (s.product L).HasPositiveFloor) := by
  refine ⟨s.product_mass L, s.product_mean_vector L, s.product_centeredGram L,
    s.product_gain L, ?_, fun hs => s.product_even hs L,
    fun hs => s.product_positiveFloor hs L⟩
  intro i a D hD
  exact s.product_inverse_nonconstant_le L i a hD

end SchauderTranslates
