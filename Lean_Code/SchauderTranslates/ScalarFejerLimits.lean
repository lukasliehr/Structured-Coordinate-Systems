import Lean_Code.SchauderTranslates.ScalarFejer
import Lean_Code.SchauderTranslates.GramPrefixStability

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Centering is a continuous finite algebraic operation once the positive mass is fixed. -/
theorem fejer_centeredGram_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) :
    Tendsto (fun N => (s.fejer hb hf N).centeredGram) atTop (𝓝 s.centeredGram) := by
  let F : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun B =>
    (s.mass : ℂ)⁻¹ • (B.submatrix Sum.inr Sum.inr - (s.mass : ℂ)⁻¹ •
      Matrix.vecMulVec (fun i => B (Sum.inr i) (Sum.inl ()))
        (star (fun i => B (Sum.inr i) (Sum.inl ()))))
  have hc : Continuous F := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [F, Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    fun_prop
  have he (N : ℕ) : (s.fejer hb hf N).centeredGram = F (s.fejer hb hf N).rawGram := by
    simp only [centeredGram, rawCenteredGram, nonconstantGram, fejer_mass, F]
    rfl
  simp_rw [he]
  exact hc.continuousAt.tendsto.comp (s.fejer_rawGram_tendsto hb hf)

/-- The normalized gain is also readable directly from the constant raw inverse entry. -/
theorem gain_eq_mass_inverse_constant (s : ScalarData d n) :
    s.gain = s.mass * (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re - 1 := by
  have h := congrArg Complex.re s.rawGram_inverse_constant_gain
  simp only [Complex.ofReal_re] at h
  have hm := s.toTorusWeight.mass_pos
  rw [h]
  field_simp
  ring

theorem fejer_gain_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) :
    Tendsto (fun N => (s.fejer hb hf N).gain) atTop (𝓝 s.gain) := by
  simp_rw [gain_eq_mass_inverse_constant, fejer_mass]
  have h := s.fejer_rawGram_inverse_tendsto hb hf
  have hi := (continuous_apply (Sum.inl ())).tendsto _ |>.comp
    ((continuous_apply (Sum.inl ())).tendsto _ |>.comp h)
  exact tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp hi) |>.sub tendsto_const_nhds

/-- Centered prefix bounds retain any strictly larger squared constant for sufficiently late means. -/
theorem fejer_centered_prefix_eventually (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hp : s.CenteredPrefixSqBound q) :
    ∀ᶠ N in atTop, (s.fejer hb hf N).CenteredPrefixSqBound r := by
  have he := eventually_all_finite_prefix_bounds (fun N => (s.fejer hb hf N).centeredGram_posDef)
    s.centeredGram_posDef (s.fejer_centeredGram_tendsto hb hf) hq hqr
    ((s.centeredPrefixSqBound_iff_gram hq).mp hp)
  filter_upwards [he] with N hN
  exact ((s.fejer hb hf N).centeredPrefixSqBound_iff_gram (hq.trans hqr.le)).mpr hN

end ScalarData
end SchauderTranslates
