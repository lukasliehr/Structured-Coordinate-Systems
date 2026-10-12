import Lean_Code.SchauderTranslates.SeedCaptureSpectrum
import Lean_Code.SchauderTranslates.SoftLossScale

noncomputable section
open Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

theorem seed_scaled_spectral_bounds (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) (m : ℝ)
    (hB : ((m : ℂ) • seedBlock i₀ L κ).PosDef)
    (hB1 : (1 - (m : ℂ) • seedBlock i₀ L κ).PosSemidef) :
    (0 < m * seedGamma κ L ∧ m * seedGamma κ L ≤ 1) ∧
      (0 < m * seedBigGamma κ L ∧ m * seedBigGamma κ L ≤ 1) := by
  have hω : 0 < seedOmega κ L ∧ seedOmega κ L < 1 :=
    seedSpectralMass_bounds (seed_a_bounds hκ0 hκ1).1 (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  let x : ι ⊕ Fin L → ℂ := Sum.elim (Pi.single i₀ 1) 0
  have hp0 : seedFullLowerProjection i₀ κ L *ᵥ x ≠ 0 := by
    intro hz
    have hh := congrFun hz (Sum.inl i₀)
    change (seedFullLowerProjection i₀ κ L *ᵥ Sum.elim (Pi.single i₀ 1) (0 : Fin L → ℂ)) (Sum.inl i₀) = 0 at hh
    rw [seedFullLowerProjection_carrier] at hh
    simp only [ite_true, Pi.single_eq_same, mul_one] at hh
    exact (ne_of_gt hω.1) (Complex.ofReal_eq_zero.mp hh)
  have hq0 : seedFullUpperProjection i₀ κ L *ᵥ x ≠ 0 := by
    intro hz
    have hh := congrFun hz (Sum.inl i₀)
    change (seedFullUpperProjection i₀ κ L *ᵥ Sum.elim (Pi.single i₀ 1) (0 : Fin L → ℂ)) (Sum.inl i₀) = 0 at hh
    rw [seedFullUpperProjection_carrier] at hh
    simp only [ite_true, Pi.single_eq_same, mul_one] at hh
    have he : (seedOmega κ L : ℂ) = 1 := (sub_eq_zero.mp hh).symm
    have he' : seedOmega κ L = 1 := by exact_mod_cast he
    exact hω.2.ne he'
  have hp : ((m : ℂ) • seedBlock i₀ L κ) *ᵥ (seedFullLowerProjection i₀ κ L *ᵥ x) =
      ((m * seedGamma κ L : ℝ) : ℂ) • (seedFullLowerProjection i₀ κ L *ᵥ x) := by
    simpa only [Pi.smul_def, Complex.real_smul, smul_eq_mul] using seedLower_scaled_eigen i₀ hκ0 hκ1 hL m x
  have hq : ((m : ℂ) • seedBlock i₀ L κ) *ᵥ (seedFullUpperProjection i₀ κ L *ᵥ x) =
      ((m * seedBigGamma κ L : ℝ) : ℂ) • (seedFullUpperProjection i₀ κ L *ᵥ x) := by
    simpa only [Pi.smul_def, Complex.real_smul, smul_eq_mul] using seedUpper_scaled_eigen i₀ hκ0 hκ1 hL m x
  exact ⟨positive_contraction_eigenvalue_bounds hB hB1 hp hp0,
    positive_contraction_eigenvalue_bounds hB hB1 hq hq0⟩

/-- The two-point spectral average is bounded above by its lower-eigenvalue capture,
and below by three quarters of it once the spectral mass has that lower bound. -/
theorem seedCaptureValue_bounds {G : Matrix α α ℂ} (hG : G.PosDef) (hG1 : (1 - G).PosSemidef)
    (b : α → ℂ) (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) {m : ℝ} (hm : 0 < m)
    (hB : ((m : ℂ) • seedBlock i₀ L κ).PosDef)
    (hB1 : (1 - (m : ℂ) • seedBlock i₀ L κ).PosSemidef)
    (hω : (3 / 4 : ℝ) ≤ seedOmega κ L) :
    (3 / 4 : ℝ) * softCapture G b (m * seedGamma κ L) ≤ seedCaptureValue G b κ m L ∧
      seedCaptureValue G b κ m L ≤ softCapture G b (m * seedGamma κ L) := by
  have hβ := seed_scaled_spectral_bounds i₀ hκ0 hκ1 hL m hB hB1
  have ho := seedEigenvalues_bounds (seed_a_bounds hκ0 hκ1).1
    (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  have hω1 : seedOmega κ L < 1 :=
    (seedSpectralMass_bounds (seed_a_bounds hκ0 hκ1).1 (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)).2
  have hlo := softCapture_nonneg hG b hβ.1.1.le hβ.1.2
  have hhi := softCapture_nonneg hG b hβ.2.1.le hβ.2.2
  have horder : softCapture G b (m * seedBigGamma κ L) ≤ softCapture G b (m * seedGamma κ L) :=
    softCapture_antitone hG hG1 b ⟨hβ.1.1.le, hβ.1.2⟩ ⟨hβ.2.1.le, hβ.2.2⟩
      (mul_le_mul_of_nonneg_left ho.2.2.2.le hm.le)
  unfold seedCaptureValue
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hω1.le) hhi,
      mul_nonneg (sub_nonneg.mpr hω) hlo]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hω1.le) (sub_nonneg.mpr horder)]

theorem seedOmega_eventually_three_quarters {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ L in atTop, (3 / 4 : ℝ) ≤ seedOmega κ L :=
  (seedOmega_tendsto_one hκ0 hκ1).eventually_const_le (by norm_num)

theorem softLossOmega_eventually_three_quarters {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (3 / 4 : ℝ) ≤ seedOmega κ (softLossLength ε) :=
  (softLossOmega_tendsto hκ0 hκ1).eventually_const_le (by norm_num)

end SchauderTranslates
