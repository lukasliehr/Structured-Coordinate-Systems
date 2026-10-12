import Lean_Code.SchauderTranslates.CutoffProductStep
import Lean_Code.SchauderTranslates.RareParameter

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Every actual finite cutoff gain is bounded by the full activation gain. -/
theorem cutoffGain_le_limit (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    s.cutoffGain hb hfloor p N ≤ s.activationLimitGain p := by
  obtain ⟨hm, ht⟩ := s.cutoffGain_tendsto hb hfloor hp0 hp1
  exact hm.ge_of_tendsto ht N

/-- Choose a finite symmetric cutoff in any strict relative interval below the limit. -/
theorem exists_relative_cutoff (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (he : 0 < ε) (hgain : 0 < s.activationLimitGain p) :
    ∃ N : ℕ, (1 - ε / 4) * s.activationLimitGain p < s.cutoffGain hb hfloor p N ∧
      s.cutoffGain hb hfloor p N ≤ s.activationLimitGain p := by
  have hlo : (1 - ε / 4) * s.activationLimitGain p < s.activationLimitGain p := by
    nlinarith [mul_pos he hgain]
  obtain ⟨N, hN⟩ := s.exists_cutoffGain_gt hb hfloor hp0 hp1 hlo
  exact ⟨N, hN, s.cutoffGain_le_limit hb hfloor hp0 hp1 N⟩

/-- Existence of the parameter and finite cutoff required by one scalar-induction step.
The finite inverse-excess bound `C` is arbitrary; no uniform dimension-dependent bound is needed. -/
theorem exists_small_relative_cutoff (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {ε C δ : ℝ} (hm : s.mass = 1 - ε)
    (he : 0 < ε) (he1 : ε < 1) (hZ : 0 < s.gain) (hδ : 0 < δ) :
    ∃ (p : ℝ) (N : ℕ), 0 < p ∧ p ≤ 1 / 100 ∧ p ≤ ε / (s.gain + ε) ∧
      p * C ≤ ε / 100 ∧ 0 < rareGain ε s.gain p ∧ rareGain ε s.gain p < δ ∧
      (1 - ε / 4) * rareGain ε s.gain p < s.cutoffGain hb hfloor p N ∧
      s.cutoffGain hb hfloor p N ≤ rareGain ε s.gain p := by
  obtain ⟨p, hp, hpmax, hpe, hpC, hgp, hgδ⟩ := exists_small_rare_parameter (C := C) he he1 hZ hδ
  have heq := s.activationLimitGain_eq_rareGain hm p
  obtain ⟨N, hNlo, hNhi⟩ := s.exists_relative_cutoff hb hfloor hp.le (by linarith) he
    (heq.symm ▸ hgp)
  rw [heq] at hNlo hNhi
  exact ⟨p, N, hp, hpmax, hpe, hpC, hgp, hgδ, hNlo, hNhi⟩

end ScalarData
end SchauderTranslates
