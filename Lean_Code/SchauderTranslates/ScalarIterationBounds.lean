import Lean_Code.SchauderTranslates.ScalarNumerics

noncomputable section
open Filter
open scoped Topology

namespace SchauderTranslates

/-- The deficit decrease telescopes with its terminal value retained. -/
theorem scalar_deficit_telescope (ε : ℕ → ℝ)
    (hstep : ∀ n, ε (n + 1) ≤ ε n - 3 * ε n ^ 2 / 4) (N : ℕ) :
    (3 / 4 : ℝ) * ∑ n ∈ Finset.range N, ε n ^ 2 ≤ ε 0 - ε N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := hstep N
      nlinarith

/-- Summability and decay use only the positive quadratic deficit decrease. -/
theorem scalar_deficit_summable_tendsto (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n)
    (hstep : ∀ n, ε (n + 1) ≤ ε n - 3 * ε n ^ 2 / 4) :
    Antitone ε ∧ Summable (fun n => ε n ^ 2) ∧
    (∑' n, ε n ^ 2) ≤ (4 / 3 : ℝ) * ε 0 ∧ Tendsto ε atTop (𝓝 0) := by
  have hanti : Antitone ε := antitone_nat_of_succ_le (fun n => by
    have h := hstep n
    nlinarith [sq_nonneg (ε n)])
  have hsum (N : ℕ) : ∑ n ∈ Finset.range N, ε n ^ 2 ≤ (4 / 3 : ℝ) * ε 0 := by
    have h := scalar_deficit_telescope ε hstep N
    nlinarith [he N]
  have hs : Summable (fun n => ε n ^ 2) :=
    summable_of_sum_range_le (fun n => sq_nonneg _) hsum
  have ht : Tendsto ε atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
    simpa only [Function.comp_def, Real.sqrt_sq (he _), Real.sqrt_zero] using ht
  exact ⟨hanti, hs, Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) hsum, ht⟩

/-- The geometric schedule spends at most one quarter of the initial gain. -/
theorem scalar_gain_budget (a : ℕ → ℝ) {Z₀ : ℝ} (hZ : 0 ≤ Z₀)
    (ha : ∀ n, a (n + 1) ≤ Z₀ / 8 * (1 / 2 : ℝ) ^ n) (N : ℕ) :
    ∑ n ∈ Finset.range N, a (n + 1) ≤ Z₀ / 4 := by
  have hgeom : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, Z₀ / 8 * (1 / 2 : ℝ) ^ n :=
      Finset.sum_le_sum (fun n _ => ha n)
    _ = Z₀ / 8 * (2 * (1 - (1 / 2 : ℝ) ^ N)) := by rw [← Finset.mul_sum, hgeom]
    _ ≤ _ := by nlinarith [mul_nonneg hZ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N)]

/-- Gain loss is controlled by the scheduled sum at every finite stage. -/
theorem scalar_gain_retained (Z a : ℕ → ℝ) (hZ : 0 ≤ Z 0)
    (ha : ∀ n, a (n + 1) ≤ Z 0 / 8 * (1 / 2 : ℝ) ^ n)
    (hstep : ∀ n, Z n - a (n + 1) ≤ Z (n + 1)) (N : ℕ) :
    3 * Z 0 / 4 ≤ Z N := by
  have htel : Z 0 - (∑ n ∈ Finset.range N, a (n + 1)) ≤ Z N := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have h := hstep N
        linarith
  have hsum := scalar_gain_budget a hZ ha N
  linarith

/-- The individual copy gains have a uniform partial-sum budget, including the initial block. -/
theorem scalar_copy_gain_budget (a : ℕ → ℝ) {Z₀ : ℝ} (hZ : 0 ≤ Z₀)
    (ha0 : a 0 = Z₀) (ha : ∀ n, a (n + 1) ≤ Z₀ / 8 * (1 / 2 : ℝ) ^ n) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n ≤ 3 * Z₀ / 2 := by
  cases N with
  | zero => simp; positivity
  | succ N =>
      rw [Finset.sum_range_succ', ha0]
      have hsum := scalar_gain_budget a hZ ha N
      linarith

/-- The centered prefix recurrence has the stated uniform bound, by finite telescoping;
no hypothesis that a later prefix constant is already small is used. -/
theorem scalar_prefix_budget (q a ε : ℕ → ℝ) {Z₀ : ℝ} (hZ : 0 ≤ Z₀)
    (hq0 : q 0 = 2) (ha0 : a 0 = Z₀)
    (ha : ∀ n, a (n + 1) ≤ Z₀ / 8 * (1 / 2 : ℝ) ^ n)
    (he : ∀ n, 0 ≤ ε n) (hε : ∀ n, ε (n + 1) ≤ ε n - 3 * ε n ^ 2 / 4)
    (hq : ∀ n, q (n + 1) ≤ q n + 10 * a n + ε n ^ 2 / 2) (N : ℕ) :
    q N ≤ 2 + 15 * Z₀ + (2 / 3 : ℝ) * ε 0 := by
  have htel : q N ≤ 2 + 10 * (∑ n ∈ Finset.range N, a n) +
      (∑ n ∈ Finset.range N, ε n ^ 2) / 2 := by
    induction N with
    | zero => simpa using hq0.le
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have h := hq N
        linarith
  have ha' := scalar_copy_gain_budget a hZ ha0 ha N
  have he' := scalar_deficit_telescope ε hε N
  nlinarith [he N]

end SchauderTranslates
