import Lean_Code.SchauderTranslates.SeedSpectralProjection

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def seedCoupling (κ : ℝ) (L : ℕ) : ℝ := Real.sqrt (L : ℝ) * κ

def seedGamma (κ : ℝ) (L : ℕ) : ℝ := seedLowerEigenvalue (1 - κ ^ 2) (seedCoupling κ L)
def seedBigGamma (κ : ℝ) (L : ℕ) : ℝ := seedUpperEigenvalue (1 - κ ^ 2) (seedCoupling κ L)
def seedRatio (κ : ℝ) (L : ℕ) : ℝ := (seedGamma κ L)⁻¹
def seedOmega (κ : ℝ) (L : ℕ) : ℝ := seedSpectralMass (1 - κ ^ 2) (seedCoupling κ L)

@[simp] theorem seedCoupling_sq (κ : ℝ) (L : ℕ) : seedCoupling κ L ^ 2 = (L : ℝ) * κ ^ 2 := by
  rw [seedCoupling, mul_pow, Real.sq_sqrt (Nat.cast_nonneg L)]

theorem seedCoupling_pos {κ : ℝ} (hκ : 0 < κ) {L : ℕ} (hL : 0 < L) : 0 < seedCoupling κ L :=
  mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hL)) hκ

theorem seed_a_bounds {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) : 0 < 1 - κ ^ 2 ∧ 1 - κ ^ 2 < 1 := by
  constructor <;> nlinarith [sq_pos_of_pos hκ0]

theorem seed_spectral_order {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) :
    0 < seedGamma κ L ∧ seedGamma κ L < 1 ∧ 1 < seedBigGamma κ L ∧ seedGamma κ L < seedBigGamma κ L :=
  seedEigenvalues_bounds (seed_a_bounds hκ0 hκ1).1 (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)

theorem seedBigGamma_linear_bounds {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) :
    (κ ^ 2 / 2) * (L : ℝ) ≤ seedBigGamma κ L ∧
      seedBigGamma κ L ≤ (κ ^ 2 + 2) * (L : ℝ) := by
  have h := seedUpperEigenvalue_trace_bounds (seed_a_bounds hκ0 hκ1).1
    (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  rw [seedCoupling_sq] at h
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  dsimp only [seedBigGamma]
  constructor <;> nlinarith [(seed_a_bounds hκ0 hκ1).1, sq_nonneg κ]

theorem seedRatio_eq {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (L : ℕ) :
    seedRatio κ L = seedBigGamma κ L / (1 - κ ^ 2) := by
  simp only [seedRatio, seedGamma, seedLowerEigenvalue, seedBigGamma, inv_div]

theorem seedRatio_linear_bounds {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) :
    (κ ^ 2 / (2 * (1 - κ ^ 2))) * (L : ℝ) ≤ seedRatio κ L ∧
      seedRatio κ L ≤ ((κ ^ 2 + 2) / (1 - κ ^ 2)) * (L : ℝ) := by
  have ha := (seed_a_bounds hκ0 hκ1).1
  have h := seedBigGamma_linear_bounds hκ0 hκ1 hL
  rw [seedRatio_eq hκ0 hκ1]
  constructor
  · apply (le_div_iff₀ ha).mpr
    have he : κ ^ 2 / (2 * (1 - κ ^ 2)) * (L : ℝ) * (1 - κ ^ 2) = κ ^ 2 / 2 * (L : ℝ) := by field_simp
    rw [he]
    exact h.1
  · apply (div_le_iff₀ ha).mpr
    have he : ((κ ^ 2 + 2) / (1 - κ ^ 2)) * (L : ℝ) * (1 - κ ^ 2) = (κ ^ 2 + 2) * (L : ℝ) := by field_simp
    rw [he]
    exact h.2

theorem seedBigGamma_tendsto_atTop {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (seedBigGamma κ) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : 0 < κ ^ 2 / 2)
  apply tendsto_atTop_mono' atTop _ h
  filter_upwards [eventually_ge_atTop 1] with L hL
  exact (seedBigGamma_linear_bounds hκ0 hκ1 hL).1

theorem seedGamma_tendsto_zero {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (seedGamma κ) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp (seedBigGamma_tendsto_atTop hκ0 hκ1)
  change Tendsto (fun L => (1 - κ ^ 2) / seedBigGamma κ L) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul h : Tendsto (fun L => (1 - κ ^ 2) * (seedBigGamma κ L)⁻¹) atTop (𝓝 ((1 - κ ^ 2) * 0)))

theorem seedRatio_tendsto_atTop {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (seedRatio κ) atTop atTop := by
  have h := (seedBigGamma_tendsto_atTop hκ0 hκ1).const_mul_atTop (inv_pos.mpr (seed_a_bounds hκ0 hκ1).1)
  change Tendsto (fun L => seedRatio κ L) atTop atTop
  simp_rw [seedRatio_eq hκ0 hκ1]
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The spectral mass of the distinguished carrier direction tends to one. -/
theorem seedOmega_tendsto_one {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (seedOmega κ) atTop (𝓝 1) := by
  have hΓ := seedBigGamma_tendsto_atTop hκ0 hκ1
  have hγ := seedGamma_tendsto_zero hκ0 hκ1
  have hd : Tendsto (fun L => seedBigGamma κ L - seedGamma κ L) atTop atTop := by
    simpa only [sub_eq_add_neg] using hΓ.atTop_add hγ.neg
  have hnum : Tendsto (fun L => 1 - seedGamma κ L) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hγ : Tendsto (fun L => (1 : ℝ) - seedGamma κ L) atTop (𝓝 (1 - 0)))
  have hsmall := hnum.div_atTop hd
  have hlim : Tendsto (fun L => 1 - (1 - seedGamma κ L) / (seedBigGamma κ L - seedGamma κ L)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hsmall
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hb := seed_spectral_order hκ0 hκ1 hL
  have hn := (sub_pos.mpr hb.2.2.2).ne'
  change _ = (seedBigGamma κ L - 1) / (seedBigGamma κ L - seedGamma κ L)
  field_simp
  ring

end SchauderTranslates
