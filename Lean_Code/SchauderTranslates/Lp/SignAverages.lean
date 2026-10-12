import Lean_Code.SchauderTranslates.Lp.DisjointNorm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Independent sign sums, retaining multiplicity when different signs give
the same vector. There are exactly 2ⁿ equally weighted outcomes. -/
def signedSums {E : Type*} [AddCommGroup E] (u : ℕ → E) : ℕ → Multiset E
  | 0 => {0}
  | n + 1 => (signedSums u n).map (fun v => v + u n) +
      (signedSums u n).map (fun v => v - u n)

theorem signedSums_card {E : Type*} [AddCommGroup E] (u : ℕ → E) (n : ℕ) :
    (signedSums u n).card = 2 ^ n := by
  induction n with
  | zero => simp [signedSums]
  | succ n ih => simp [signedSums, ih, pow_succ, Nat.mul_two]

theorem sign_pair_square_sum (s : Multiset ℂ) (w : ℂ) :
    (s.map (fun v => ‖v + w‖ ^ 2)).sum + (s.map (fun v => ‖v - w‖ ^ 2)).sum =
      2 * ((s.map (fun v => ‖v‖ ^ 2)).sum + (s.card : ℝ) * ‖w‖ ^ 2) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons v s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    nlinarith [parallelogram_law_with_norm ℂ v w]

/-- The square average identity for complex scalars; no real-valuedness assumption. -/
theorem signed_sum_square_identity (u : ℕ → ℂ) (n : ℕ) :
    ((signedSums u n).map (fun v => ‖v‖ ^ 2)).sum =
      (2 : ℝ) ^ n * ∑ j ∈ Finset.range n, ‖u j‖ ^ 2 := by
  induction n with
  | zero => simp [signedSums]
  | succ n ih =>
    simp only [signedSums, Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add]
    rw [sign_pair_square_sum, ih, signedSums_card, Nat.cast_pow, Nat.cast_ofNat,
      Finset.sum_range_succ, pow_succ]
    ring

theorem norm_sq_rpow (z : ℂ) (P : ℝ) : (‖z‖ ^ (2 : ℕ)) ^ (P / 2) = ‖z‖ ^ P := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
  congr 1
  norm_num <;> ring

/-- The two-point Jensen inequality and the parallelogram law give the
lower Clarkson inequality at every real exponent P ≥ 2. -/
theorem complex_clarkson_lower {P : ℝ} (hP : 2 ≤ P) (z w : ℂ) :
    2 * (‖z‖ ^ P + ‖w‖ ^ P) ≤ ‖z + w‖ ^ P + ‖z - w‖ ^ P := by
  have hs : 1 ≤ P / 2 := by linarith
  have hj := (convexOn_rpow hs).2 (sq_nonneg ‖z + w‖) (sq_nonneg ‖z - w‖)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) * ‖z + w‖ ^ 2 + (1 / 2 : ℝ) * ‖z - w‖ ^ 2 =
      ‖z‖ ^ 2 + ‖w‖ ^ 2 := by nlinarith [parallelogram_law_with_norm ℂ z w]
  change ((1 / 2 : ℝ) * ‖z + w‖ ^ 2 + (1 / 2 : ℝ) * ‖z - w‖ ^ 2) ^ (P / 2) ≤
    (1 / 2 : ℝ) * (‖z + w‖ ^ 2) ^ (P / 2) + (1 / 2 : ℝ) * (‖z - w‖ ^ 2) ^ (P / 2) at hj
  rw [he, norm_sq_rpow, norm_sq_rpow] at hj
  have hlow := Real.add_rpow_le_rpow_add (sq_nonneg ‖z‖) (sq_nonneg ‖w‖) hs
  rw [norm_sq_rpow, norm_sq_rpow] at hlow
  linarith

theorem sign_pair_power_lower {P : ℝ} (hP : 2 ≤ P) (s : Multiset ℂ) (w : ℂ) :
    2 * ((s.map (fun v => ‖v‖ ^ P)).sum + (s.card : ℝ) * ‖w‖ ^ P) ≤
      (s.map (fun v => ‖v + w‖ ^ P)).sum + (s.map (fun v => ‖v - w‖ ^ P)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons v s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    linarith [complex_clarkson_lower hP v w]

/-- Finite independent-sign average dominates the sum of individual Pth powers. -/
theorem signed_sum_power_lower {P : ℝ} (hP : 2 ≤ P) (u : ℕ → ℂ) (n : ℕ) :
    (2 : ℝ) ^ n * (∑ j ∈ Finset.range n, ‖u j‖ ^ P) ≤
      ((signedSums u n).map (fun v => ‖v‖ ^ P)).sum := by
  induction n with
  | zero => simp [signedSums, ne_of_gt (show 0 < P from by linarith)]
  | succ n ih =>
    have hs := sign_pair_power_lower hP (signedSums u n) (u n)
    rw [signedSums_card, Nat.cast_pow, Nat.cast_ofNat] at hs
    simp only [signedSums, Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add]
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]

theorem normed_sign_pair_power_lower {E : Type*} [NormedAddCommGroup E] {P : ℝ}
    (hcl : ∀ v w : E, 2 * (‖v‖ ^ P + ‖w‖ ^ P) ≤ ‖v + w‖ ^ P + ‖v - w‖ ^ P)
    (s : Multiset E) (w : E) :
    2 * ((s.map (fun v => ‖v‖ ^ P)).sum + (s.card : ℝ) * ‖w‖ ^ P) ≤
      (s.map (fun v => ‖v + w‖ ^ P)).sum + (s.map (fun v => ‖v - w‖ ^ P)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons v s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    linarith [hcl v w]

theorem normed_signed_sum_power_lower {E : Type*} [NormedAddCommGroup E] {P : ℝ}
    (hP : 0 < P)
    (hcl : ∀ v w : E, 2 * (‖v‖ ^ P + ‖w‖ ^ P) ≤ ‖v + w‖ ^ P + ‖v - w‖ ^ P)
    (u : ℕ → E) (n : ℕ) :
    (2 : ℝ) ^ n * (∑ j ∈ Finset.range n, ‖u j‖ ^ P) ≤
      ((signedSums u n).map (fun v => ‖v‖ ^ P)).sum := by
  induction n with
  | zero => simp [signedSums, hP.ne']
  | succ n ih =>
    have hs := normed_sign_pair_power_lower hcl (signedSums u n) (u n)
    rw [signedSums_card, Nat.cast_pow, Nat.cast_ofNat] at hs
    simp only [signedSums, Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add]
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]

theorem lp_clarkson_lower {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hpfin : p ≠ ∞)
    (f g : LebesgueLp p) :
    2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ≤
      ‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpR : (2 : ℝ) ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_le_toReal (by norm_num) hpfin).mpr hp
  have hpoint : ∀ᵐ x ∂MeasureTheory.volume,
      2 * (‖f x‖ ^ p.toReal + ‖g x‖ ^ p.toReal) ≤
        ‖(f + g) x‖ ^ p.toReal + ‖(f - g) x‖ ^ p.toReal := by
    filter_upwards [MeasureTheory.Lp.coeFn_add f g, MeasureTheory.Lp.coeFn_sub f g] with x ha hs
    simpa only [ha, hs, Pi.add_apply, Pi.sub_apply] using complex_clarkson_lower hpR (f x) (g x)
  have hf := integrable_norm_rpow f hp0 hpfin
  have hg := integrable_norm_rpow g hp0 hpfin
  have hfg := integrable_norm_rpow (f + g) hp0 hpfin
  have hfm := integrable_norm_rpow (f - g) hp0 hpfin
  have hi := MeasureTheory.integral_mono_ae ((hf.add hg).const_mul 2) (hfg.add hfm) hpoint
  change (∫ x, 2 * (‖f x‖ ^ p.toReal + ‖g x‖ ^ p.toReal)) ≤
    (∫ x, ‖(f + g) x‖ ^ p.toReal + ‖(f - g) x‖ ^ p.toReal) at hi
  rw [integral_const_mul, integral_add hf hg, integral_add hfg hfm,
    integral_norm_rpow f hp0 hpfin, integral_norm_rpow g hp0 hpfin,
    integral_norm_rpow (f + g) hp0 hpfin, integral_norm_rpow (f - g) hp0 hpfin] at hi
  exact hi

theorem lp_signed_sum_power_lower {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hpfin : p ≠ ∞)
    (u : ℕ → LebesgueLp p) (n : ℕ) :
    (2 : ℝ) ^ n * (∑ j ∈ Finset.range n, ‖u j‖ ^ p.toReal) ≤
      ((signedSums u n).map (fun v => ‖v‖ ^ p.toReal)).sum :=
  normed_signed_sum_power_lower
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpfin)
    (lp_clarkson_lower hp hpfin) u n

end SchauderTranslates.LpConstruction
