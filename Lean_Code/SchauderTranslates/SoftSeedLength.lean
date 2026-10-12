import Lean_Code.SchauderTranslates.SeedSpectralLimits

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The paper's seed count, with `X = log (1 / ε)`. -/
def softSeedLength (X : ℝ) : ℕ := ⌊X / (4 * Real.log 2)⌋₊

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem softSeedLength_upper {X : ℝ} (hX : 0 ≤ X) :
    (softSeedLength X : ℝ) ≤ X / (4 * Real.log 2) :=
  Nat.floor_le (by positivity)

theorem softSeedLength_lower {X : ℝ} (hX : 8 * Real.log 2 ≤ X) :
    X / (8 * Real.log 2) ≤ (softSeedLength X : ℝ) := by
  have hl := log_two_pos
  have hf := Nat.lt_floor_add_one (X / (4 * Real.log 2))
  have hden : 0 < 4 * Real.log 2 := by positivity
  have hden' : 0 < 8 * Real.log 2 := by positivity
  apply (div_le_iff₀ hden').mpr
  have h := (div_lt_iff₀ hden).mp hf
  dsimp only [softSeedLength]
  nlinarith

theorem softSeedLength_pos {X : ℝ} (hX : 8 * Real.log 2 ≤ X) : 0 < softSeedLength X := by
  have hl := log_two_pos
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h := lt_of_lt_of_le (div_pos hX0 (by positivity)) (softSeedLength_lower hX)
  exact_mod_cast h

theorem softSeedLength_tendsto : Tendsto softSeedLength atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (max (8 * Real.log 2) ((n : ℝ) * (8 * Real.log 2)))] with X hX
  have hl := log_two_pos
  have h := softSeedLength_lower ((le_max_left _ _).trans hX)
  have hn : (n : ℝ) ≤ X / (8 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (le_max_right _ _).trans hX
  exact_mod_cast hn.trans h

def softSeedRatio (κ X : ℝ) : ℝ := seedRatio κ (softSeedLength X)

def softRatioLower (κ : ℝ) : ℝ := κ ^ 2 / (2 * (1 - κ ^ 2)) / (8 * Real.log 2)
def softRatioUpper (κ : ℝ) : ℝ := (κ ^ 2 + 2) / (1 - κ ^ 2) / (4 * Real.log 2)

theorem softRatio_constants_pos {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    0 < softRatioLower κ ∧ 0 < softRatioUpper κ := by
  have ha := (seed_a_bounds hκ0 hκ1).1
  have hl := log_two_pos
  unfold softRatioLower softRatioUpper
  constructor <;> positivity

/-- Quantitative comparison with the logarithmic loss scale. -/
theorem softSeedRatio_linear_bounds {κ X : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hX : 8 * Real.log 2 ≤ X) :
    softRatioLower κ * X ≤ softSeedRatio κ X ∧ softSeedRatio κ X ≤ softRatioUpper κ * X := by
  have hL := softSeedLength_pos hX
  have h := seedRatio_linear_bounds hκ0 hκ1 hL
  have ha := (seed_a_bounds hκ0 hκ1).1
  have hl := log_two_pos
  have hX0 : 0 ≤ X := (by positivity : 0 ≤ 8 * Real.log 2).trans hX
  constructor
  · have hb := mul_le_mul_of_nonneg_left (softSeedLength_lower hX)
      (by positivity : 0 ≤ κ ^ 2 / (2 * (1 - κ ^ 2)))
    calc
      softRatioLower κ * X = (κ ^ 2 / (2 * (1 - κ ^ 2))) * (X / (8 * Real.log 2)) := by unfold softRatioLower; ring
      _ ≤ _ := hb
      _ ≤ _ := h.1
  · have hb := mul_le_mul_of_nonneg_left (softSeedLength_upper hX0)
      (by positivity : 0 ≤ (κ ^ 2 + 2) / (1 - κ ^ 2))
    calc
      softSeedRatio κ X ≤ _ := h.2
      _ ≤ _ := hb
      _ = softRatioUpper κ * X := by unfold softRatioUpper; ring

theorem softSeedRatio_tendsto {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (softSeedRatio κ) atTop atTop :=
  (seedRatio_tendsto_atTop hκ0 hκ1).comp softSeedLength_tendsto

/-- The allowed seed mass is at least the fourth-root loss scale. -/
theorem softSeedLength_mass_bound {X : ℝ} (hX : 0 ≤ X) :
    Real.exp (-X / 4) ≤ (1 / 2 : ℝ) ^ softSeedLength X := by
  have hl := log_two_pos
  have hL := softSeedLength_upper hX
  have he : (1 / 2 : ℝ) ^ softSeedLength X = Real.exp (-(softSeedLength X : ℝ) * Real.log 2) := by
    rw [show -(softSeedLength X : ℝ) * Real.log 2 = (softSeedLength X : ℝ) * (-Real.log 2) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div]
  rw [he, Real.exp_le_exp]
  have h := (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mp hL
  nlinarith

end SchauderTranslates
