import Lean_Code.SchauderTranslates.Lp.RootFiniteCoefficients
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Finite multiplier bound used by the normalized unconditional root system. -/
def FiniteMultiplierBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℕ → E) (H : ℝ) : Prop :=
  ∀ (n : ℕ) (c a : ℕ → ℂ), (∀ j, ‖a j‖ ≤ 1) →
    ‖∑ j ∈ Finset.range n, (a j * c j) • f j‖ ≤ H * ‖∑ j ∈ Finset.range n, c j • f j‖

theorem finite_multiplier_on_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℕ → E) {H : ℝ} (hH : FiniteMultiplierBound f H) (c : ℕ → ℂ) {x : E}
    (hconv : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, c j • f j) atTop (𝓝 x))
    (n : ℕ) (ε : ℕ → ℂ) (hε : ∀ j, ‖ε j‖ ≤ 1) :
    ‖∑ j ∈ Finset.range n, (ε j * c j) • f j‖ ≤ H * ‖x‖ := by
  let a : ℕ → ℂ := fun j => if j < n then ε j else 0
  have ha : ∀ j, ‖a j‖ ≤ 1 := by intro j; dsimp [a]; split_ifs; exact hε j; simp
  have ht : Tendsto (fun m : ℕ => H * ‖∑ j ∈ Finset.range m, c j • f j‖)
      atTop (𝓝 (H * ‖x‖)) := tendsto_const_nhds.mul hconv.norm
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  have he : (∑ j ∈ Finset.range m, (a j * c j) • f j) =
      ∑ j ∈ Finset.range n, (ε j * c j) • f j := by
    calc
      _ = ∑ j ∈ Finset.range n, (a j * c j) • f j := by
        symm
        apply Finset.sum_subset (Finset.range_mono hm)
        intro j _ hj
        have hn : ¬j < n := by simpa using hj
        simp [a, hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [a, Finset.mem_range.mp hj]
  have hb := hH m c a ha
  rwa [he] at hb

/-- Blueprint `lp:root-coefficients`. Every ordered norm-convergent root
expansion has ℓᵖ coefficients with norm bounded by H times the vector norm. -/
theorem root_coefficient_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hpfin : p ≠ ∞)
    (f : ℕ → LebesgueLp p) (hf : ∀ j, ‖f j‖ = 1) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : FiniteMultiplierBound f H) (c : ℕ → ℂ) {x : LebesgueLp p}
    (hconv : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, c j • f j) atTop (𝓝 x)) :
    ∃ hc : Memℓp c p, ‖(⟨c, hc⟩ : lp (fun _ : ℕ => ℂ) p)‖ ≤ H * ‖x‖ := by
  have hpR := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpfin
  have hbound (n : ℕ) : (∑ j ∈ Finset.range n, ‖c j‖ ^ p.toReal) ≤ (H * ‖x‖) ^ p.toReal :=
    finite_root_coefficient_bound hp hpfin f hf c n
      (fun ε hε => finite_multiplier_on_expansion f hH c hconv n ε hε)
  have hsum : Summable (fun j => ‖c j‖ ^ p.toReal) :=
    summable_of_sum_range_le (fun j => Real.rpow_nonneg (norm_nonneg _) _) hbound
  have hc : Memℓp c p := memℓp_gen hsum
  refine ⟨hc, ?_⟩
  apply lp.norm_le_of_tsum_le hpR (mul_nonneg hH0 (norm_nonneg x))
  exact hsum.tsum_le_of_sum_range_le hbound

end SchauderTranslates.LpConstruction
