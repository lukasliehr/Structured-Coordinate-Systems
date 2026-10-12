import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open scoped BigOperators

namespace SchauderTranslates

def rareGain (ε Z p : ℝ) : ℝ :=
  p / (1 - ε) * (Z + ε ^ 2 - p * ε * (Z + ε))

theorem rareGain_bounds {ε Z p : ℝ}
    (he : 0 < ε) (he1 : ε < 1) (hZ : 0 < Z) (hp : 0 < p)
    (hpe : p ≤ ε / (Z + ε)) :
    p * Z ≤ rareGain ε Z p * (1 - ε) ∧
      rareGain ε Z p * (1 - ε) ≤ p * (Z + ε ^ 2) := by
  have hd : 0 < Z + ε := by positivity
  have hm : 1 - ε ≠ 0 := by linarith
  have hid : rareGain ε Z p * (1 - ε) =
      p * (Z + ε ^ 2 - p * ε * (Z + ε)) := by
    unfold rareGain
    field_simp
  rw [hid]
  have hc := (le_div_iff₀ hd).mp hpe
  have hc' : 0 ≤ ε ^ 2 - p * ε * (Z + ε) := by nlinarith
  constructor
  · nlinarith [mul_nonneg hp.le hc']
  · nlinarith [mul_nonneg hp.le (mul_nonneg (mul_nonneg hp.le he.le) hd.le)]

theorem rareGain_pos {ε Z p : ℝ}
    (he : 0 < ε) (he1 : ε < 1) (hZ : 0 < Z) (hp : 0 < p)
    (hpe : p ≤ ε / (Z + ε)) : 0 < rareGain ε Z p := by
  have hb := (rareGain_bounds he he1 hZ hp hpe).1
  have hmul : 0 < p * Z := mul_pos hp hZ
  nlinarith

theorem floor_gain_bounds {Z z : ℝ} (hZ : 0 < Z) (hz : 0 < z) :
    Z - z < (⌊Z / z⌋₊ : ℝ) * z ∧ (⌊Z / z⌋₊ : ℝ) * z ≤ Z := by
  have hlow := (div_lt_iff₀ hz).mp (Nat.lt_floor_add_one (Z / z))
  have hup := (le_div_iff₀ hz).mp (Nat.floor_le (div_nonneg hZ.le hz.le))
  exact ⟨by linarith, hup⟩

/-- The numerical content of one activation followed by independent copies. -/
theorem copies_activation_bounds {ε Z p z : ℝ}
    (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (hZ : 1 / 646 ≤ Z) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hpe : p ≤ ε / (Z + ε))
    (hzlo : (1 - ε / 4) * rareGain ε Z p ≤ z)
    (hzhi : z ≤ rareGain ε Z p) :
    (1 / 10 : ℝ) < (⌊Z / z⌋₊ : ℝ) * p ∧
      (⌊Z / z⌋₊ : ℝ) * p ≤ 1 - 3 * ε / 4 := by
  have he1 : ε < 1 := by linarith
  have hZ0 : 0 < Z := by linarith
  have hcut : 0 < 1 - ε / 4 := by linarith
  have hmass : 0 < 1 - ε := by linarith
  have hz : 0 < z := lt_of_lt_of_le
    (mul_pos hcut (rareGain_pos he he1 hZ0 hp hpe)) hzlo
  obtain ⟨hglo, hghi⟩ := rareGain_bounds he he1 hZ0 hp hpe
  obtain ⟨hfloorlo, hfloorhi⟩ := floor_gain_bounds hZ0 hz
  let L : ℝ := (⌊Z / z⌋₊ : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hzlower : p * Z * (1 - ε / 4) ≤ z * (1 - ε) := by
    have h1 := mul_le_mul_of_nonneg_right hzlo hmass.le
    have h2 := mul_le_mul_of_nonneg_right hglo hcut.le
    nlinarith
  have hzupper : z * (1 - ε) ≤ p * (Z + ε ^ 2) :=
    (mul_le_mul_of_nonneg_right hzhi hmass.le).trans hghi
  have hupper : L * p ≤ 1 - 3 * ε / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hzlower hL
    have h2 := mul_le_mul_of_nonneg_right hfloorhi hmass.le
    have hs : Z * (L * p * (1 - ε / 4)) ≤ Z * (1 - ε) := by
      dsimp [L] at *
      nlinarith
    have hs' := le_of_mul_le_mul_left hs hZ0
    calc
      L * p ≤ (1 - ε) / (1 - ε / 4) := (le_div_iff₀ hcut).mpr hs'
      _ ≤ 1 - 3 * ε / 4 := (div_le_iff₀ hcut).mpr (by nlinarith [sq_nonneg ε])
  have hden : 0 < Z + ε ^ 2 := by positivity
  have hlower : (1 - ε) * Z / (Z + ε ^ 2) - p < L * p := by
    have h1 := mul_le_mul_of_nonneg_left hzupper (show 0 ≤ L + 1 by positivity)
    have h2 := mul_lt_mul_of_pos_right hfloorlo hmass
    have hs : (1 - ε) * Z < (L + 1) * p * (Z + ε ^ 2) := by
      dsimp [L] at *
      nlinarith
    have hs' := (div_lt_iff₀ hden).mpr hs
    linarith
  have hratio : (9 / 10 : ℝ) / (1 + 646 / 100) ≤ (1 - ε) * Z / (Z + ε ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have hs : ε ^ 2 ≤ 1 / 100 := by nlinarith
    have h1 : ε ^ 2 ≤ (646 / 100) * Z := by linarith
    have h2 := mul_le_mul_of_nonneg_right hemax hZ0.le
    norm_num at ⊢
    nlinarith
  constructor
  · change 1 / 10 < L * p
    linarith
  · exact hupper

theorem bernoulli_loss_bounds {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    (N : ℝ) * a / (1 + N * a) ≤ 1 - (1 - a) ^ N ∧
      1 - (1 - a) ^ N ≤ N * a := by
  have hprod : (1 + (N : ℝ) * a) * (1 - a) ^ N ≤ 1 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (1 - a) ^ N := pow_nonneg (sub_nonneg.mpr ha1) _
      have hs : 0 ≤ ((N : ℝ) + 1) * a ^ 2 * (1 - a) ^ N := by positivity
      nlinarith
  have hden : 0 < 1 + (N : ℝ) * a := by positivity
  constructor
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  · have h := one_add_mul_le_pow (a := -a) (by linarith : -2 ≤ -a) N
    simp only [← sub_eq_add_neg, mul_neg] at h
    linarith

theorem scalar_mass_step {ε p : ℝ} (N : ℕ)
    (he : 0 < ε) (hemax : ε ≤ 1 / 10) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hlo : (1 / 10 : ℝ) < N * p) (hhi : (N : ℝ) * p ≤ 1 - 3 * ε / 4) :
    ε / 12 ≤ 1 - (1 - p * ε) ^ N ∧
      1 - (1 - p * ε) ^ N ≤ ε - 3 * ε ^ 2 / 4 := by
  have ha : 0 ≤ p * ε := (mul_pos hp he).le
  have ha1 : p * ε ≤ 1 := by nlinarith
  obtain ⟨hl, hu⟩ := bernoulli_loss_bounds ha ha1 N
  have hNp : 0 ≤ (N : ℝ) * p := by positivity
  have hnum : (N : ℝ) * (p * ε) ≤ ε := by nlinarith
  have hsmall : 0 ≤ 1 - (1 - p * ε) ^ N :=
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr ha1) (by linarith))
  have hden : 0 < 1 + (N : ℝ) * (p * ε) := by positivity
  have hlo' := (div_le_iff₀ hden).mp hl
  have h1 : ε / 10 < (N : ℝ) * (p * ε) := by nlinarith
  have h2 := mul_nonneg hsmall (show 0 ≤ 1 / 10 - (N : ℝ) * (p * ε) by linarith)
  constructor
  · nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi he.le
    nlinarith

theorem scalar_inverse_excess_step {ε ε' p C y : ℝ}
    (he : 0 < ε) (hemax : ε ≤ 1 / 10) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hlo : ε / 12 ≤ ε') (hhi : ε' ≤ ε)
    (hC : p * C ≤ ε / 100)
    (hy : y ≤ (1 - p * ε) * (1 + p * C) / (1 - ε')) : y - 1 < 2 * ε' := by
  have hm : 0 ≤ 1 - p * ε := by nlinarith
  have hm1 : 1 - p * ε ≤ 1 := by nlinarith
  have he' : 0 < ε' := by linarith
  have hd : 0 < 1 - ε' := by linarith
  have hc := mul_le_mul_of_nonneg_left (add_le_add_left hC 1) hm
  have hnum : (1 - p * ε) * (1 + p * C) ≤ 1 + ε / 100 := by
    nlinarith [mul_nonneg (show 0 ≤ p * ε by positivity) (show 0 ≤ 1 + ε / 100 by positivity)]
  have hb := (le_div_iff₀ hd).mp hy
  have hesq : ε' ^ 2 ≤ ε' / 10 := by nlinarith
  nlinarith

/-- All scalar rare-step inequalities, with the inverse-diagonal estimate supplied
by the separate Gram-matrix calculation. No analytic or matrix conclusion is assumed here. -/
theorem scalar_step_numerics {ε Z p z : ℝ}
    (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (hZ : 1 / 646 ≤ Z) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hpe : p ≤ ε / (Z + ε))
    (hzlo : (1 - ε / 4) * rareGain ε Z p ≤ z)
    (hzhi : z ≤ rareGain ε Z p) :
    let L := ⌊Z / z⌋₊
    let ε' := 1 - (1 - p * ε) ^ L
    Z - z < (L : ℝ) * z ∧ (L : ℝ) * z ≤ Z ∧
    (1 / 10 : ℝ) < (L : ℝ) * p ∧ (L : ℝ) * p ≤ 1 - 3 * ε / 4 ∧
    ε / 12 ≤ ε' ∧ ε' ≤ ε - 3 * ε ^ 2 / 4 ∧
    ∀ C y : ℝ, p * C ≤ ε / 100 →
      y ≤ (1 - p * ε) * (1 + p * C) / (1 - ε') → y - 1 < 2 * ε' := by
  dsimp only
  have hZ0 : 0 < Z := by linarith
  have hz : 0 < z := lt_of_lt_of_le
    (mul_pos (by linarith : 0 < 1 - ε / 4)
      (rareGain_pos he (by linarith) hZ0 hp hpe)) hzlo
  obtain ⟨hfl, hfu⟩ := floor_gain_bounds hZ0 hz
  obtain ⟨hl, hu⟩ := copies_activation_bounds he hemax hZ hp hpmax hpe hzlo hzhi
  obtain ⟨hml, hmu⟩ := scalar_mass_step ⌊Z / z⌋₊ he hemax hp hpmax hl hu
  refine ⟨hfl, hfu, hl, hu, hml, hmu, ?_⟩
  intro C y hC hy
  exact scalar_inverse_excess_step he hemax hp hpmax hml
    (by nlinarith [sq_nonneg ε]) hC hy

end SchauderTranslates
