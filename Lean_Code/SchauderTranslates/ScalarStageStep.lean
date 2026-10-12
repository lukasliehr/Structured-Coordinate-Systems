import Lean_Code.SchauderTranslates.ScalarStage
import Lean_Code.SchauderTranslates.ScalarRowBounds
import Lean_Code.SchauderTranslates.CutoffChoice

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarStage

/-- One full choice step: actual finite torus data, the ordered-prefix budget, and all
inverse/positivity estimates are constructed together. -/
theorem exists_next {k : ℕ} (s : ScalarStage k) :
    ∃ t : ScalarStage (k + 1), s.ε / 12 ≤ t.ε ∧ t.ε ≤ s.ε - 3 * s.ε ^ 2 / 4 ∧
      t.data.gain ≤ s.data.gain ∧ t.q = s.q + 10 * s.η + s.ε ^ 2 / 2 ∧
      t.η ≤ (1 / 323) / 8 * (1 / 2) ^ k := by
  obtain ⟨b, hb, hfloor⟩ := s.positiveFloor
  let C : ℝ := ∑ j : Unit ⊕ Fin s.length, |(s.data.rawGram⁻¹ j j).re - 1|
  have hC (j : Unit ⊕ Fin s.length) : (s.data.rawGram⁻¹ j j).re - 1 ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg
      ((s.data.rawGram⁻¹ i i).re - 1)) (Finset.mem_univ j))
  let δ : ℝ := (1 / 323) / 8 * (1 / 2) ^ k
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨p, N, hp, hpmax, hpe, hpC, hgp, hgδ, hlo, hhi⟩ :=
    s.data.exists_small_relative_cutoff (C := C) hb hfloor s.mass_eq s.deficit_pos
      (by linarith [s.deficit_le]) (by linarith [s.gain_admissible]) hδ
  have hp1 : p ≤ 1 := by linarith
  let cut := s.data.orderedCutoffData p N
  have hcutgain : cut.gain = s.data.cutoffGain hb hfloor p N :=
    s.data.cutoffData_gain hb hfloor hp.le hp1 N (ScalarData.orderedCutoffEquiv s.length N)
  have hcutlo : (1 - s.ε / 4) * rareGain s.ε s.data.gain p ≤ cut.gain := by
    rw [hcutgain]
    exact hlo.le
  have hcuthi : cut.gain ≤ rareGain s.ε s.data.gain p := by
    rw [hcutgain]
    exact hhi
  have hη : cut.gain ≤ δ := hcuthi.trans hgδ.le
  let L := ⌊s.data.gain / cut.gain⌋₊
  let next := cut.product L
  let ε' := 1 - next.mass
  let q' := s.q + 10 * s.η + s.ε ^ 2 / 2
  have hstep := s.data.cutoff_product_step hb hfloor s.mass_eq s.deficit_pos s.deficit_le
    s.gain_admissible s.gain_upper hp hpmax hpe s.inverse_norm N
    (ScalarData.orderedCutoffEquiv s.length N) hcutlo hcuthi
  change 0 < ε' ∧ s.ε / 12 ≤ ε' ∧ ε' ≤ s.ε - 3 * s.ε ^ 2 / 4 ∧
    s.data.gain - cut.gain < next.gain ∧ next.gain ≤ s.data.gain ∧
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) next.rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 ∧
    (∀ C : ℝ, (∀ j, (s.data.rawGram⁻¹ j j).re - 1 ≤ C) → p * C ≤ s.ε / 100 →
      ∀ i, (next.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 < 2 * ε') at hstep
  obtain ⟨hepos, helo, hedec, hgloss, hgupper, hinorm, hidiag⟩ := hstep
  have hbudget : q' + (2 / 3) * ε' + 10 * cut.gain ≤
      scalarPrefixBudget - (5 / 323) * (1 / 2) ^ (k + 1) :=
    scalar_stage_budget_step s.budget hedec hη
  have hq2 : 2 ≤ q' := by dsimp [q']; nlinarith [s.q_lower, s.η_nonneg, sq_nonneg s.ε]
  have hq3 : q' < 3 := by
    have hpw : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
    nlinarith [cut.gain_nonneg, scalarPrefixBudget_lt_three]
  have hcutprefix : cut.CenteredPrefixSqBound q' :=
    s.data.orderedCutoffData_prefix_step s.even hb hfloor hp.le hp1 N s.deficit_pos.le
      s.deficit_le s.mass_eq s.gain_upper (by linarith [s.q_lower, s.η_nonneg])
      s.augmented s.inverse_excess
  have hcutEven : cut.IsEven :=
    s.data.activationData_even s.even p _ Subtype.val_injective
      (ScalarData.cutoffConstantIndex s.length N).2 rfl (ScalarData.orderedCutoffEquiv s.length N)
  have hcutFloor : cut.HasPositiveFloor :=
    s.data.activationData_positiveFloor s.positiveFloor p _ Subtype.val_injective
      (ScalarData.cutoffConstantIndex s.length N).2 rfl (ScalarData.orderedCutoffEquiv s.length N)
  have hgainupper : next.gain ≤ 1 / 323 := hgupper.trans s.gain_upper
  have hLgain : (L : ℝ) * cut.gain ≤ 1 / 323 := by
    rw [← cut.product_gain L]
    exact hgainupper
  let t : ScalarStage (k + 1) := {
    dimension := L * (s.dimension + 1)
    length := L * Fintype.card (ScalarData.CutoffNonconstant s.length N)
    data := next
    ε := ε'
    q := q'
    η := cut.gain
    deficit_pos := hepos
    deficit_le := by nlinarith [s.deficit_le, sq_nonneg s.ε]
    mass_eq := by dsimp [ε']; ring
    even := cut.product_even hcutEven L
    positiveFloor := cut.product_positiveFloor hcutFloor L
    gain_lower := scalar_stage_gain_step s.gain_lower hgloss.le hη
    gain_upper := hgainupper
    inverse_norm := hinorm
    inverse_excess := fun i => (hidiag C hC hpC i).le
    q_lower := hq2
    η_nonneg := cut.gain_nonneg
    centered := cut.product_centered_prefix L (by linarith) hcutprefix
    augmented := cut.product_augmented_prefix L hq2 hq3 hLgain hcutprefix
    budget := hbudget }
  exact ⟨t, helo, hedec, hgupper, rfl, hη⟩

end ScalarStage
end SchauderTranslates
