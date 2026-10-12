import Lean_Code.SchauderTranslates.ScalarFloorNumerics
import Lean_Code.SchauderTranslates.ScalarRowNumerics

/-!
# Real arithmetic for the sharp scalar induction

The paper fixes `0 < d ≤ 1`, puts `t = d / 4`, `a₀ = t / 100`, and runs the scalar induction
with the initial circle weight `1 - a₀ + a₀ cos (2 π x)`. This file collects the parameters
and every purely numerical inequality of that induction (paper: `h2:ss:scalar-induction`).
The statements are the parametrized counterparts of `ScalarNumerics`, `ScalarFloorNumerics`,
`ScalarRowNumerics` and `ScalarStageBudget`, whose absolute constants `1/323`, `1/646`,
`2 ≤ q < 3` and `10` are replaced by `Z₀`, a relative bound, `1 + t ≤ q < 1 + 2 t` and `5 / t`.
-/

noncomputable section
namespace SchauderTranslates.Sharp.Scalar
open SchauderTranslates

/-- The amplitude `a₀ = t / 100` of the initial circle weight. -/
def sharpA (t : ℝ) : ℝ := t / 100

/-- The initial gain `Z₀ = a₀² / (4 - 8 a₀ + 3 a₀²)`. -/
def sharpZ (t : ℝ) : ℝ := sharpA t ^ 2 / (4 - 8 * sharpA t + 3 * sharpA t ^ 2)

/-- The total centered-prefix budget `1 + t + 15 Z₀ / (2 t) + 2 a₀ / 3`. -/
def sharpBudget (t : ℝ) : ℝ :=
  1 + t + (3 / 2) * ((5 / t) * sharpZ t) + (2 / 3) * sharpA t

theorem sharpA_pos {t : ℝ} (ht0 : 0 < t) : 0 < sharpA t := by
  unfold sharpA
  positivity

theorem sharpA_le {t : ℝ} (ht1 : t ≤ 1 / 4) : sharpA t ≤ 1 / 400 := by
  unfold sharpA
  linarith

theorem sharpA_le_tenth {t : ℝ} (ht1 : t ≤ 1 / 4) : sharpA t ≤ 1 / 10 :=
  (sharpA_le ht1).trans (by norm_num)

theorem sharpZ_denominator {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    3 ≤ 4 - 8 * sharpA t + 3 * sharpA t ^ 2 ∧ 4 - 8 * sharpA t + 3 * sharpA t ^ 2 ≤ 4 := by
  have ha0 := sharpA_pos ht0
  have ha1 := sharpA_le ht1
  constructor <;> nlinarith [sq_nonneg (sharpA t)]

/-- Paper: `a₀² / 4 ≤ Z₀ ≤ a₀² / 3`. -/
theorem sharpZ_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    sharpA t ^ 2 / 4 ≤ sharpZ t ∧ sharpZ t ≤ sharpA t ^ 2 / 3 := by
  obtain ⟨hl, hu⟩ := sharpZ_denominator ht0 ht1
  have hd : 0 < 4 - 8 * sharpA t + 3 * sharpA t ^ 2 := by linarith
  have hsq : 0 ≤ sharpA t ^ 2 := sq_nonneg _
  unfold sharpZ
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hd]
    nlinarith
  · rw [div_le_div_iff₀ hd (by norm_num)]
    nlinarith

theorem sharpZ_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : 0 < sharpZ t := by
  have h := (sharpZ_bounds ht0 ht1).1
  have ha := sharpA_pos ht0
  have : 0 < sharpA t ^ 2 / 4 := by positivity
  linarith

theorem sharpZ_le_sq {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    sharpZ t ≤ (1 / 400) ^ 2 / 3 := by
  have h := (sharpZ_bounds ht0 ht1).2
  have ha0 := sharpA_pos ht0
  have ha1 := sharpA_le ht1
  have hs : sharpA t ^ 2 ≤ (1 / 400) ^ 2 := pow_le_pow_left₀ ha0.le ha1 2
  linarith

theorem sharpZ_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : sharpZ t ≤ 1 :=
  (sharpZ_le_sq ht0 ht1).trans (by norm_num)

/-- Paper: `Z₀ < t / 2`, the margin in the hypothesis `Q > 1 + Z` of the copies lemma. -/
theorem sharpZ_le_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : sharpZ t ≤ t / 2 := by
  have h := (sharpZ_bounds ht0 ht1).2
  have hs : sharpA t ^ 2 / 3 ≤ t / 2 := by
    unfold sharpA
    nlinarith
  linarith

/-- The scaled copy cost of the initial gain: `(5 / t) Z₀ ≤ t / 6000`. -/
theorem sharp_copy_cost_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    (5 / t) * sharpZ t ≤ t / 6000 := by
  have h := (sharpZ_bounds ht0 ht1).2
  have h5 : (0 : ℝ) ≤ 5 / t := by positivity
  calc
    (5 / t) * sharpZ t ≤ (5 / t) * (sharpA t ^ 2 / 3) := mul_le_mul_of_nonneg_left h h5
    _ = t / 6000 := by
      unfold sharpA
      field_simp
      ring

theorem sharp_copy_cost_nonneg {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    0 ≤ (5 / t) * sharpZ t :=
  mul_nonneg (by positivity) (sharpZ_pos ht0 ht1).le

/-- Paper `h2:eq:qbound`: the whole centered budget stays strictly below `1 + 2 t`. -/
theorem sharpBudget_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : sharpBudget t < 1 + 2 * t := by
  have h := sharp_copy_cost_le ht0 ht1
  unfold sharpBudget sharpA
  linarith

/-- The activation count has the two-sided bound of the paper (`h2:eq:Lp`), assuming only
that the squared deficit is at most `16 / 3` times the gain. -/
theorem copies_activation_bounds_sharp {ε Z p z : ℝ}
    (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (hZ0 : 0 < Z) (hZε : ε ^ 2 ≤ (16 / 3) * Z) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hpe : p ≤ ε / (Z + ε))
    (hzlo : (1 - ε / 4) * rareGain ε Z p ≤ z)
    (hzhi : z ≤ rareGain ε Z p) :
    (1 / 10 : ℝ) < (⌊Z / z⌋₊ : ℝ) * p ∧
      (⌊Z / z⌋₊ : ℝ) * p ≤ 1 - 3 * ε / 4 := by
  have he1 : ε < 1 := by linarith
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
  have hratio : (27 / 190 : ℝ) ≤ (1 - ε) * Z / (Z + ε ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have h2 := mul_le_mul_of_nonneg_right hemax hZ0.le
    nlinarith
  constructor
  · change 1 / 10 < L * p
    linarith
  · exact hupper

/-- All scalar rare-step inequalities in the relative range of the sharp induction. -/
theorem scalar_step_numerics_sharp {ε Z p z : ℝ}
    (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (hZ0 : 0 < Z) (hZε : ε ^ 2 ≤ (16 / 3) * Z) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
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
  have hz : 0 < z := lt_of_lt_of_le
    (mul_pos (by linarith : 0 < 1 - ε / 4)
      (rareGain_pos he (by linarith) hZ0 hp hpe)) hzlo
  obtain ⟨hfl, hfu⟩ := floor_gain_bounds hZ0 hz
  obtain ⟨hl, hu⟩ := copies_activation_bounds_sharp he hemax hZ0 hZε hp hpmax hpe hzlo hzhi
  obtain ⟨hml, hmu⟩ := scalar_mass_step ⌊Z / z⌋₊ he hemax hp hpmax hl hu
  refine ⟨hfl, hfu, hl, hu, hml, hmu, ?_⟩
  intro C y hC hy
  exact scalar_inverse_excess_step he hemax hp hpmax hml
    (by nlinarith [sq_nonneg ε]) hC hy

/-- The inverse-norm implication after the block estimate, for any retained gain `Z ≤ 1`
(paper: `1 / (2 ε) > 1 + Z₀`). -/
theorem scalar_floor_norm_step_sharp {x y h h' Z : ℝ} (hx : 0 < x) (hxmax : x ≤ 1 / 10)
    (hy : 0 < y) (hymax : y ≤ x - 3 * x ^ 2 / 4) (hZ : Z ≤ 1)
    (hh : h ≤ x⁻¹ ^ 2) (hh' : h' ≤ (h + 1 + Z) / (1 - y)) :
    h' ≤ y⁻¹ ^ 2 := by
  have hyx : y ≤ x := by nlinarith [sq_nonneg x]
  have hm : 0 < 1 - y := by linarith
  have hmargin := scalar_floor_reciprocal_margin hx hxmax hy hymax
  have hlarge : (5 : ℝ) ≤ 1 / (2 * x) :=
    (le_div_iff₀ (by positivity : 0 < 2 * x)).mpr (by linarith)
  have hu : h + 1 + Z ≤ (1 - y) / y ^ 2 := by
    rw [inv_pow, ← one_div] at hh
    linarith
  calc
    h' ≤ (h + 1 + Z) / (1 - y) := hh'
    _ ≤ ((1 - y) / y ^ 2) / (1 - y) := div_le_div_of_nonneg_right hu hm.le
    _ = y⁻¹ ^ 2 := by field_simp

/-- Paper: the constant row has squared bound at most `1 + a₀² < 1 + t`. -/
theorem scalar_constant_row_sharp {t ε Z : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ sharpA t) (hZ : 0 ≤ Z) (hZ1 : Z ≤ sharpZ t) :
    1 + Z + ε * (Z + ε) / (4 * (1 - ε)) ≤ 1 + t := by
  have ha0 := sharpA_pos ht0
  have ha1 := sharpA_le ht1
  have hZa := hZ1.trans (sharpZ_bounds ht0 ht1).2
  have hd : 0 < 4 * (1 - ε) := by linarith
  have hsq : 0 ≤ sharpA t ^ 2 := sq_nonneg _
  have h1 : ε * Z ≤ sharpA t * (sharpA t ^ 2 / 3) := mul_le_mul hε1 hZa hZ ha0.le
  have h2 : ε ^ 2 ≤ sharpA t ^ 2 := pow_le_pow_left₀ hε hε1 2
  have h3 : sharpA t * (sharpA t ^ 2 / 3) ≤ sharpA t ^ 2 / 1200 := by nlinarith
  have h4 : sharpA t ^ 2 * ε ≤ sharpA t ^ 2 * (1 / 400) :=
    mul_le_mul_of_nonneg_left (hε1.trans ha1) hsq
  have hsmall : ε * (Z + ε) / (4 * (1 - ε)) ≤ sharpA t ^ 2 / 3 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hat : sharpA t ^ 2 ≤ t := by
    unfold sharpA
    nlinarith
  linarith

/-- Paper: `Q² / (Q - 1 - Z) < 5 / t` in the range `1 + t ≤ Q < 1 + 2 t`, `Z ≤ t / 2`. -/
theorem sharp_copy_prefix_cost {t q Z η : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4)
    (hq : 1 + t ≤ q) (hq2 : q < 1 + 2 * t) (hZ : Z ≤ t / 2) (hη : 0 ≤ η) :
    q + q ^ 2 * η / (q - 1 - Z) ≤ q + (5 / t) * η := by
  have hd : 0 < q - 1 - Z := by linarith
  have hq2' : q ^ 2 ≤ 9 / 4 := by nlinarith
  have hkey : q ^ 2 ≤ (5 / t) * (q - 1 - Z) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ht0]
    nlinarith
  apply add_le_add le_rfl
  rw [div_le_iff₀ hd]
  have h := mul_le_mul_of_nonneg_right hkey hη
  calc
    q ^ 2 * η ≤ (5 / t) * (q - 1 - Z) * η := h
    _ = (5 / t) * η * (q - 1 - Z) := by ring

/-- A reserve in the combined prefix/deficit budget makes the induction noncircular.
Here `κ` is the cost per unit of copy gain (`5 / t`) and `B` the total budget. -/
theorem sharp_stage_budget_step {k : ℕ} {κ Z B ε ε' q η η' : ℝ} (hκ : 0 ≤ κ) (hZ : 0 ≤ Z)
    (hbudget : q + (2 / 3) * ε + κ * η ≤ B - (1 / 2) * (κ * Z) * (1 / 2) ^ k)
    (he : ε' ≤ ε - 3 * ε ^ 2 / 4)
    (hη : η' ≤ Z / 8 * (1 / 2) ^ k) :
    (q + κ * η + ε ^ 2 / 2) + (2 / 3) * ε' + κ * η' ≤
      B - (1 / 2) * (κ * Z) * (1 / 2) ^ (k + 1) := by
  rw [pow_succ (1 / 2 : ℝ) k]
  have hn : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  have h1 : κ * η' ≤ κ * (Z / 8 * (1 / 2) ^ k) := mul_le_mul_of_nonneg_left hη hκ
  have h2 : 0 ≤ (κ * Z) * (1 / 2) ^ k := mul_nonneg (mul_nonneg hκ hZ) hn
  nlinarith

/-- The matching gain reserve pays for the new copy's gain loss at each stage. -/
theorem sharp_stage_gain_step {k : ℕ} {Z₀ Z Z' η' : ℝ}
    (hZ : (3 / 4) * Z₀ + (1 / 4) * Z₀ * (1 / 2) ^ k ≤ Z)
    (hloss : Z - η' ≤ Z') (hη : η' ≤ Z₀ / 8 * (1 / 2) ^ k) :
    (3 / 4) * Z₀ + (1 / 4) * Z₀ * (1 / 2) ^ (k + 1) ≤ Z' := by
  rw [pow_succ (1 / 2 : ℝ) k]
  linarith

/-- In the sharp range the squared deficit is at most `16 / 3` times the retained gain
(paper: `Z ≥ 3 Z₀ / 4 ≥ 3 a₀² / 16` and `ε ≤ a₀`). -/
theorem sharp_deficit_sq_le {t ε Z : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ sharpA t) (hZ : (3 / 4) * sharpZ t ≤ Z) :
    ε ^ 2 ≤ (16 / 3) * Z := by
  have h2 : ε ^ 2 ≤ sharpA t ^ 2 := pow_le_pow_left₀ hε hε1 2
  have h := (sharpZ_bounds ht0 ht1).1
  linarith

end SchauderTranslates.Sharp.Scalar
