import Lean_Code.SchauderTranslates.ScalarStageStep
import Lean_Code.SchauderTranslates.ScalarIterationBounds
import Lean_Code.SchauderTranslates.InverseNormFloor

noncomputable section
open Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarStage

/-- The next stage is chosen only from the fully proved finite construction. -/
def next {k : ℕ} (s : ScalarStage k) : ScalarStage (k + 1) := Classical.choose s.exists_next

theorem next_deficit_decrease {k : ℕ} (s : ScalarStage k) :
    s.next.ε ≤ s.ε - 3 * s.ε ^ 2 / 4 := (Classical.choose_spec s.exists_next).2.1

def sequence : (k : ℕ) → ScalarStage k
  | 0 => initial
  | k + 1 => (sequence k).next

theorem sequence_deficit_tendsto :
    Antitone (fun k => (sequence k).ε) ∧ Tendsto (fun k => (sequence k).ε) atTop (𝓝 0) := by
  obtain ⟨ha, _, _, ht⟩ := scalar_deficit_summable_tendsto (fun k => (sequence k).ε)
    (fun k => (sequence k).deficit_pos.le) (fun k => (sequence k).next_deficit_decrease)
  exact ⟨ha, ht⟩

theorem centered_budget {k : ℕ} (s : ScalarStage k) : s.q ≤ scalarPrefixBudget := by
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith [s.budget, s.deficit_pos, s.η_nonneg]

theorem gain_retained {k : ℕ} (s : ScalarStage k) : (3 / 4) * (1 / 323) ≤ s.data.gain := by
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith [s.gain_lower]

theorem augmented_sqrt_three {k : ℕ} (s : ScalarStage k) :
    s.data.AugmentedPrefixSqBound ((Real.sqrt 3) ^ 2) := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact FinitePrefixSqBound.mono s.augmented s.augmented_budget_lt_three.le

theorem inverse_constant_lt_two {k : ℕ} (s : ScalarStage k) :
    (s.data.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  rw [s.data.rawGram_inverse_constant_gain, Complex.ofReal_re, s.mass_eq]
  apply (div_lt_iff₀ (by linarith [s.deficit_le] : 0 < 1 - s.ε)).mpr
  linarith [s.deficit_le, s.gain_upper]

end ScalarStage

/-- Even measurable scalar blocks with vanishing deficit, retained gain, both ordered
prefix bounds, and the raw inverse/spectral estimates required by smoothing and selection.
All norms and Grams refer to the actual finite characters of the displayed torus densities. -/
theorem measurable_scalar_blocks :
    ∃ (d n : ℕ → ℕ) (s : (j : ℕ) → ScalarData (d j) (n j)) (ε q : ℕ → ℝ) (K : ℝ),
      Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧ 0 ≤ K ∧ K < 2 ∧
      ∀ j, (s j).IsEven ∧ (s j).HasPositiveFloor ∧
        0 < ε j ∧ ε j ≤ 1 / 10 ∧ (s j).mass = 1 - ε j ∧
        (3 / 4) * (1 / 323) ≤ (s j).gain ∧ (s j).gain ≤ 1 / 323 ∧
        (∀ i : Fin (n j), ((s j).rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * ε j) ∧
        ((s j).rawGram - (((ε j) ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
        2 ≤ q j ∧ q j ≤ 2 + 15 / 323 + 1 / 15 ∧ q j < 3 ∧
        (s j).CenteredPrefixSqBound (q j) ∧ (s j).AugmentedPrefixSqBound (K ^ 2) ∧
        ((s j).rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  let S := ScalarStage.sequence
  refine ⟨fun j => (S j).dimension, fun j => (S j).length, fun j => (S j).data,
    fun j => (S j).ε, fun j => (S j).q, Real.sqrt 3,
    ScalarStage.sequence_deficit_tendsto.1, ScalarStage.sequence_deficit_tendsto.2,
    Real.sqrt_nonneg 3, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · intro j
    exact ⟨(S j).even, (S j).positiveFloor, (S j).deficit_pos, (S j).deficit_le, (S j).mass_eq,
      (S j).gain_retained, (S j).gain_upper, (S j).inverse_excess,
      inverse_norm_matrix_floor (S j).data.rawGram_posDef (S j).deficit_pos (S j).inverse_norm,
      (S j).q_lower, (S j).centered_budget, (S j).q_lt_three, (S j).centered,
      (S j).augmented_sqrt_three, (S j).inverse_constant_lt_two⟩

end SchauderTranslates
